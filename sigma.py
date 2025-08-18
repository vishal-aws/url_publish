import json
import time
import logging
import sys
import os
import io
 
# Force UTF-8 encoding for Windows services
if sys.platform == "win32":
    sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')
    sys.stderr = io.TextIOWrapper(sys.stderr.buffer, encoding='utf-8')
    os.environ['PYTHONIOENCODING'] = 'utf-8'

import pandas as pd
import requests
import re
import base64
from datetime import datetime, timedelta, timezone
from urllib.parse import urlparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import TimeoutException, WebDriverException, NoSuchElementException
from selenium.webdriver.chrome.service import Service as ChromeService
from PIL import Image
import numpy as np
import msal
from logging.handlers import RotatingFileHandler
import uuid
import socket
import unicodedata

# VM Resource monitoring
try:
    import psutil
    PSUTIL_AVAILABLE = True
except ImportError:
    PSUTIL_AVAILABLE = False
    print("⚠️ psutil not installed. Install with: pip install psutil")

# Optional dependency detection for webdriver-manager
try:
    from webdriver_manager.chrome import ChromeDriverManager  # type: ignore
    WDM_AVAILABLE = True
except Exception:
    WDM_AVAILABLE = False

# ========= ENHANCED VM-OPTIMIZED CONFIGURATION ==========
class Config:
    CLIENT_ID = "a3abf39c-6206-4238-b26d-bc4f0252a57d"
    TENANT_ID = "ff355289-721e-4dd7-a663-afec62ab9d54"
    CLIENT_SECRET = "Ymv8Q~iLMAKjrq1fAz2GNhcYPIFrWRSB-~MkfduQ"

    EMAIL_SENDER = "vishal.chauhan@ltimindtree.com"
    EMAIL_RECEIVER = "vishal.chauhan@ltimindtree.com"

    # VM-Optimized Thresholds (will be adjusted dynamically)
    PAGE_LOAD_TIMEOUT = 30          # Reduced from 60
    TAB_LOAD_TIMEOUT = 25           # Reduced from 40
    SLOW_THRESHOLD = 8              # Reduced from 25
    VERY_SLOW_THRESHOLD = 15        # Reduced from 50
    CRITICAL_THRESHOLD = 25         # New: For truly broken sites
    
    MAX_WORKERS = 3                 # Reduced from 5 for VM stability
    SITES_JSON = "test_sites.json"
    EXCEL_PATH = "sites_config.xlsx"
    LOG_FILE = "monitoring.log"
    RESULTS_EXCEL = "monitoring_results.xlsx"
    SCREENSHOT_DIR = "screenshots"
    USE_HTML_EMAIL = True
    HEADLESS = True
    PAGE_EXTRA_WAIT = 1             # Reduced from 2
    SUSPECT_BODY_LENGTH = 50
    SLOW_ALERT_WHITELIST = ["snackworks.com", "snackworks.ca"]
    MAX_RETRIES = 2                 # Increased from 1 for VM issues
    RETRY_DELAY_SECONDS = 3         # Reduced from 5
    COLOR_VARIANCE_THRESHOLD = 30
    HTTP_REQUEST_TIMEOUT = 20       # Reduced from 30
    EXCEPTION_URLS = [
        "https://philadelphia-professional.de/",
        "https://www.philadelphia.co.nl/",
        "https://milka.com.tr/"
    ]

    # Enhanced monitoring
    SPA_WAIT_TIMEOUT = 8            # Reduced from 10
    VISUAL_SCORE_THRESHOLD = 4      # Reduced from 5 for better sensitivity
    ENHANCED_RETRY = True

    # Structured audit
    AUDIT_LOG = "monitoring_audit.log.jsonl"
    AUDIT_ROTATE_MB = 20
    AUDIT_BACKUPS = 10

    # Auto driver management
    USE_WEBDRIVER_MANAGER_FALLBACK = True
    WDM_CACHE_DIR = os.path.join(os.getcwd(), ".wdm-cache")
    WDM_CACHE_VALID_DAYS = 14
    CHROME_BINARY = None
    
    # VM Performance tracking
    VM_PERFORMANCE_FACTOR = 1.0
    VM_BASELINE_TIME = 0.0


# ========= LOGGING + RUN CONTEXT ==========
logger = logging.getLogger("monitor")
logger.setLevel(logging.INFO)

human_handler = RotatingFileHandler(
    Config.LOG_FILE, maxBytes=5_000_000, backupCount=5, encoding="utf-8")
human_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))

console = logging.StreamHandler()
console.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))

logger.handlers = [human_handler, console]

RUN_ID = f"{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}-{uuid.uuid4().hex[:8]}"

os.makedirs(Config.SCREENSHOT_DIR, exist_ok=True)
os.makedirs(Config.WDM_CACHE_DIR, exist_ok=True)

IST = timezone(timedelta(hours=5, minutes=30))


# ========= HELPERS ==========
def _norm(s: str) -> str:
    if not s:
        return ""
    s = unicodedata.normalize("NFKD", s)
    return (s.replace("\u2019", "'").replace("\u2018", "'")
             .replace("\u201c", '"').replace("\u201d", '"')
             .strip().lower())

def canonical_host(base_url: str) -> str:
    """Return lowercased host w/o scheme/port and w/o leading www."""
    try:
        url = (base_url or "").strip()
        if not re.match(r"^https?://", url, re.I):
            url = "http://" + url
        u = urlparse(url)
        host = (u.hostname or "").lower().strip()
        if host.startswith("www."):
            host = host[4:]
        return host or (base_url or "").strip().lower()
    except Exception:
        return (base_url or "").strip().lower()

def public_suffix_simple(host: str) -> str:
    """Best-effort public suffix: 'co.uk','com.nl' etc., else last label."""
    labels = (host or "").split(".")
    if len(labels) < 2:
        return host or ""
    if len(labels[-1]) == 2 and labels[-2] in {"co","com","org","net","gov","edu","ac"}:
        return f"{labels[-2]}.{labels[-1]}"
    return labels[-1]

def region_hint_from_host(host: str) -> str:
    """NL for *.nl, UK for *.uk, etc.; else GLOBAL."""
    labels = (host or "").split(".")
    if len(labels) >= 2 and len(labels[-1]) == 2:
        return labels[-1].upper()
    return "GLOBAL"

def detect_chrome_net_error(driver):
    try:
        url = driver.execute_script("return document.URL") or ""
        title = driver.title or ""
        code = driver.execute_script("var e=document.querySelector('#error-code');return e?e.innerText:'';") or ""
        has_wrapper = driver.execute_script(
            "return !!document.querySelector('.interstitial-wrapper,#main-message,#details-button,#reload-button')"
        )
    except Exception:
        url, title, code, has_wrapper = "", "", "", False

    if url.startswith("chrome-error://") or has_wrapper or _norm(code).startswith("err_"):
        return True, (code or "BROWSER_NET_ERROR")
    try:
        h1 = driver.execute_script("var h=document.querySelector('h1');return h? h.innerText:'';") or ""
        if "this site can't be reached" in _norm(" ".join([url, title, h1])):
            return True, (code or "BROWSER_NET_ERROR")
    except Exception:
        pass
    return False, ""


# ========= AUDIT ==========
class Audit:
    def __init__(self, path):
        self.path = path
        self.hostname = socket.gethostname()

    def _now(self):
        return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"

    def write(self, event: dict):
        base = {
            "ts": self._now(),
            "run_id": RUN_ID,
            "host": self.hostname,
            "app": "site_monitor",
            "schema_ver": "1.0",
        }
        base.update({k: v for k, v in event.items() if v is not None})
        with open(Config.AUDIT_LOG, "a", encoding="utf-8") as f:
            f.write(json.dumps(base, ensure_ascii=False, separators=(",", ":")) + "\n")

audit = Audit(Config.AUDIT_LOG)


# ========= GRAPH EMAIL ==========
def get_access_token():
    authority = f"https://login.microsoftonline.com/{Config.TENANT_ID}"
    app = msal.ConfidentialClientApplication(
        Config.CLIENT_ID, authority=authority, client_credential=Config.CLIENT_SECRET
    )
    scopes = ["https://graph.microsoft.com/.default"]
    result = app.acquire_token_for_client(scopes=scopes)
    if "access_token" in result:
        return result['access_token']
    error = result.get("error")
    desc = result.get("error_description")
    logger.error(f"❌ Failed to acquire token: {error} - {desc}")
    raise Exception(f"Failed to acquire token: {error} - {desc}")

def send_email_graph(subject, body, html=False, attachments=None):
    access_token = get_access_token()
    headers = {"Authorization": f"Bearer {access_token}", "Content-Type": "application/json"}

    graph_attachments = []
    if attachments:
        for item in attachments:
            if isinstance(item, str):
                path, display_name = item, os.path.basename(item)
            else:
                path, display_name = item.get("path"), item.get("name") or os.path.basename(item.get("path", ""))

            if not path or not os.path.exists(path):
                logger.warning(f"⚠️ Attachment file not found: {path}")
                continue

            with open(path, "rb") as f:
                bdata = f.read()

            graph_attachments.append({
                "@odata.type": "#microsoft.graph.fileAttachment",
                "name": display_name,
                "contentType": "image/png",
                "contentBytes": base64.b64encode(bdata).decode("utf-8"),
            })

    email_body = {
        "message": {
            "subject": subject,
            "body": {"contentType": "HTML" if html else "Text", "content": body},
            "toRecipients": [{"emailAddress": {"address": email}} for email in (Config.EMAIL_RECEIVER if isinstance(Config.EMAIL_RECEIVER, list) else [Config.EMAIL_RECEIVER])],
            "from": {"emailAddress": {"address": Config.EMAIL_SENDER}},
            "attachments": graph_attachments
        }
    }
    endpoint = f"https://graph.microsoft.com/v1.0/users/{Config.EMAIL_SENDER}/sendMail"

    response = requests.post(endpoint, headers=headers, json=email_body)
    if response.status_code == 202:
        logger.info("✅ Email sent via Microsoft Graph API successfully.")
    else:
        logger.error(f"❌ Failed to send email: {response.status_code} - {response.text}")
        raise Exception(f"Email sending failed: {response.status_code} - {response.text}")


# ========= UTILS ==========
def update_json_from_excel(excel_path, json_path):
    df = pd.read_excel(excel_path)
    df.columns = df.columns.str.strip().str.lower()

    def normalize_base_url(url: str) -> str:
        url = str(url).strip().rstrip('/')
        if not url.startswith(('http://', 'https://')):
            url = 'http://' + url
        return url

    def make_key(site, base_url):
        url = normalize_base_url(base_url)
        url = url.removeprefix("http://").removeprefix("https://").replace('/', '_').replace(' ', '_')
        site_part = site.strip().replace(' ', '_')
        return f"{site_part}_{url}"

    sites = {}
    for idx, row in df.iterrows():
        site = str(row['site_name']).strip() if pd.notna(row['site_name']) else ""
        base_url = str(row['base_url']).strip() if pd.notna(row['base_url']) else ""
        if not site or not base_url:
            logger.warning(f"⚠️ Skipping row {idx + 2} missing site_name/base_url")
            continue
        key = make_key(site, base_url)
        if key not in sites:
            sites[key] = {"site_name": site, "base_url": base_url, "tabs": {}}
        tab_name = row.get('tab_name', None)
        tab_url = row.get('tab_url', None)
        parent_tab = row.get('parent_tab') if 'parent_tab' in df.columns else None
        if pd.notna(tab_name) and str(tab_name).strip():
            turl = str(tab_url).strip() if pd.notna(tab_url) and str(tab_url).strip() else None
            parent = str(parent_tab).strip() if parent_tab and pd.notna(parent_tab) else None
            sites[key]["tabs"][tab_name.strip()] = {"url": turl, "parent": parent}

    with open(json_path, "w", encoding='utf-8') as f:
        json.dump(sites, f, indent=4, ensure_ascii=False)

    logger.info(f"✅ Updated {json_path} from {excel_path} — total: {len(sites)} sites")

def is_slow_whitelisted(url: str) -> bool:
    domain = urlparse(url).netloc.lower()
    if domain.startswith("www."):
        domain = domain[4:]
    return any(domain.endswith(w) for w in Config.SLOW_ALERT_WHITELIST)

def is_exception_site(url):
    url = url.lower().rstrip('/')
    for exc_url in Config.EXCEPTION_URLS:
        if url.startswith(exc_url.rstrip('/')):
            return True
    return False

def deduplicate_file_paths(paths):
    seen = set()
    deduped = []
    for p in paths:
        if p not in seen:
            deduped.append(p)
            seen.add(p)
    return deduped


# ========= ENHANCED VM-OPTIMIZED MONITOR ==========

class WebsiteMonitor:
    def __init__(self):
        self.failure_screenshots = {}  # (site_display, tab, variant) -> path
        self.screenshot_dir = Config.SCREENSHOT_DIR
        self._shot_index = {}          # NEW: (site, tab, variant, status) -> path


    def _slug(self, s: str) -> str:
        s = (s or "").strip()
        s = re.sub(r"\s+", "_", s)
        return re.sub(r"[^A-Za-z0-9_\-]+", "", s)[:80] or "NA"

    def _url_variant(self, url: str) -> str:
        path = urlparse(url).path.strip("/")
        if not path:
            return "root"
        return self._slug(path.split("/")[-1])

    def _utc_stamp(self):
        return datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%SZ")

    def _utc_stamp_ms(self):
        return datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S_%fZ")

    # ------------ CENTRALIZED AUDIT (auto-add VM-normalized fields) ------------
    def audit_site(self, **kwargs):
        """
        Emit a site_check event.
        If a load time is present (load_time_s or site_load_time),
        also emit:
          - load_time_vm_norm_s
          - vm_factor
        (Doesn't overwrite if caller already supplied them.)
        """
        lt = None
        if isinstance(kwargs.get("load_time_s"), (int, float)):
            lt = kwargs["load_time_s"]
        elif isinstance(kwargs.get("site_load_time"), (int, float)):
            lt = kwargs["site_load_time"]
        if isinstance(lt, (int, float)):
            vmf = kwargs.get("vm_factor", Config.VM_PERFORMANCE_FACTOR)
            try:
                vmf = float(vmf)
            except Exception:
                vmf = 1.0
            kwargs.setdefault("vm_factor", vmf)
            kwargs.setdefault("load_time_vm_norm_s", round(lt / max(1.0, vmf), 2))
        audit.write({"event": "site_check", **{k: v for k, v in kwargs.items() if v is not None}})

    def audit_tab(self, **kwargs):
        """
        Emit a tab_check event.
        If a load time is present (load_time_s),
        also emit:
          - load_time_vm_norm_s
          - vm_factor
        (Doesn't overwrite if caller already supplied them.)
        """
        lt = kwargs.get("load_time_s")
        if isinstance(lt, (int, float)):
            vmf = kwargs.get("vm_factor", Config.VM_PERFORMANCE_FACTOR)
            try:
                vmf = float(vmf)
            except Exception:
                vmf = 1.0
            kwargs.setdefault("vm_factor", vmf)
            kwargs.setdefault("load_time_vm_norm_s", round(lt / max(1.0, vmf), 2))
        audit.write({"event": "tab_check", **{k: v for k, v in kwargs.items() if v is not None}})

    def check_vm_health(self):
        """Monitor VM resources before starting monitoring"""
        if not PSUTIL_AVAILABLE:
            logger.warning("⚠️ psutil not installed, skipping VM health check")
            return True
            
        try:
            cpu_percent = psutil.cpu_percent(interval=2)
            memory = psutil.virtual_memory()
            disk = psutil.disk_usage('/')
            
            # Log resource status
            logger.info(f"🖥️ VM Resources: CPU={cpu_percent:.1f}%, Memory={memory.percent:.1f}%, Disk={disk.percent:.1f}%")
            
            # Check if resources are critically low
            if memory.percent > 90:
                logger.warning("⚠️ Critical memory usage detected")
                return False
            if cpu_percent > 90:
                logger.warning("⚠️ Critical CPU usage detected") 
                return False
            if disk.percent > 95:
                logger.warning("⚠️ Critical disk usage detected")
                return False
                
            # Log available memory
            available_gb = memory.available / (1024**3)
            logger.info(f"🖥️ Available Memory: {available_gb:.1f} GB")
            
            return True
            
        except Exception as e:
            logger.warning(f"⚠️ VM health check failed: {e}")
            return True

    def calibrate_vm_baseline(self):
        """Measure VM performance and adjust thresholds dynamically"""
        if not PSUTIL_AVAILABLE:
            logger.warning("⚠️ psutil not available, using default thresholds")
            return 1.0
            
        try:
            driver = None
            
            # Test with a known fast, reliable site
            test_url = "https://www.google.com"
            logger.info(f"🔧 Calibrating VM performance with {test_url}...")
            
            driver = self.create_driver()
            start_time = time.time()
            driver.get(test_url)
            self.wait_for_page_ready(driver, 10)
            baseline_time = time.time() - start_time
            driver.quit()
            
            # Get system resources
            cpu_usage = psutil.cpu_percent(interval=1)
            memory_usage = psutil.virtual_memory().percent
            
            # Calculate performance factor
            perf_factor = 1.0
            if baseline_time > 3:
                perf_factor = min(baseline_time / 3, 2.5)  # Cap at 2.5x
            if cpu_usage > 70:
                perf_factor *= 1.3
            if memory_usage > 80:
                perf_factor *= 1.2
                
            # Apply minimum factor for VM environments
            perf_factor = max(perf_factor, 1.1)  # Minimum 10% buffer for VMs
                
            # Adjust thresholds
            Config.SLOW_THRESHOLD = int(8 * perf_factor)
            Config.VERY_SLOW_THRESHOLD = int(15 * perf_factor)
            Config.CRITICAL_THRESHOLD = int(25 * perf_factor)
            Config.PAGE_LOAD_TIMEOUT = int(30 * perf_factor)
            Config.TAB_LOAD_TIMEOUT = int(25 * perf_factor)
            Config.VM_PERFORMANCE_FACTOR = perf_factor
            Config.VM_BASELINE_TIME = baseline_time
            
            logger.info(f"🔧 VM calibrated: baseline={baseline_time:.1f}s, factor={perf_factor:.1f}")
            logger.info(f"📊 Adjusted thresholds: SLOW={Config.SLOW_THRESHOLD}s, VERY_SLOW={Config.VERY_SLOW_THRESHOLD}s, CRITICAL={Config.CRITICAL_THRESHOLD}s")
            
            audit.write({
                "event": "vm_calibration",
                "baseline_time": baseline_time,
                "performance_factor": perf_factor,
                "cpu_usage": cpu_usage,
                "memory_usage": memory_usage,
                "adjusted_thresholds": {
                    "slow": Config.SLOW_THRESHOLD,
                    "very_slow": Config.VERY_SLOW_THRESHOLD,
                    "critical": Config.CRITICAL_THRESHOLD
                }
            })
            
            return perf_factor
            
        except Exception as e:
            logger.warning(f"⚠️ VM calibration failed: {e}, using default thresholds")
            if driver:
                try:
                    driver.quit()
                except:
                    pass
            return 1.0

    def _looks_like_driver_mismatch(self, e: Exception) -> bool:
        msg = (str(e) or "").lower()
        hints = [
            "this version of chromedriver", "only supports chrome version",
            "current browser version is", "session not created",
            "unable to obtain driver", "no such driver", "cannot find chrome binary",
            "chrome not reachable", "chromedriver executable needs to be available"
        ]
        return any(h in msg for h in hints)

    def create_driver(self):
        options = Options()
        options.add_argument("--window-size=1920,1080")
        options.add_argument("--disable-extensions")
        options.add_experimental_option('excludeSwitches', ['enable-logging'])
        options.add_experimental_option("prefs", {"profile.default_content_setting_values.geolocation": 1})
        
        # Enhanced VM-optimized Chrome arguments
        options.add_argument(
            "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/126.0.0.0 Safari/537.36"
        )
        
        # Core VM stability options
        options.add_argument('--no-sandbox')
        options.add_argument('--disable-dev-shm-usage')
        options.add_argument('--disable-gpu')
        options.add_argument('--disable-software-rasterizer')
        
        # Performance optimizations for VM
        options.add_argument('--disable-background-timer-throttling')
        options.add_argument('--disable-backgrounding-occluded-windows')
        options.add_argument('--disable-renderer-backgrounding')
        options.add_argument('--disable-features=TranslateUI,BlinkGenPropertyTrees')
        options.add_argument('--disable-ipc-flooding-protection')
        options.add_argument('--memory-pressure-off')
        options.add_argument('--max_old_space_size=4096')
        
        # Reduce resource usage
        options.add_argument('--aggressive-cache-discard')
        options.add_argument('--disable-background-networking')
        options.add_argument('--disable-default-apps')
        options.add_argument('--disable-sync')
        options.add_argument('--disable-translate')
        options.add_argument('--hide-scrollbars')
        options.add_argument('--metrics-recording-only')
        options.add_argument('--mute-audio')
        options.add_argument('--disable-web-security')
        options.add_argument('--disable-features=VizDisplayCompositor')
        
        if Config.HEADLESS:
            options.add_argument("--headless=new")
            
        if Config.CHROME_BINARY:
            options.binary_location = Config.CHROME_BINARY

        try:
            service = ChromeService()
            driver = webdriver.Chrome(service=service, options=options)
            driver.implicitly_wait(5)  # Reduced from 10 for VM efficiency
            logger.info("✅ Chrome started via Selenium Manager (auto driver).")
            return driver
        except WebDriverException as e:
            logger.warning(f"⚠️ Selenium Manager launch failed: {e}")

            if not (Config.USE_WEBDRIVER_MANAGER_FALLBACK and WDM_AVAILABLE and self._looks_like_driver_mismatch(e)):
                logger.error("❌ Not a driver-mismatch or webdriver-manager unavailable; re-raising.")
                raise

            try:
                os.makedirs(Config.WDM_CACHE_DIR, exist_ok=True)
                manager = ChromeDriverManager(cache_valid_range=Config.WDM_CACHE_VALID_DAYS, path=Config.WDM_CACHE_DIR)
                driver_path = manager.install()
                logger.info(f"⬇️  webdriver-manager installed driver @ {driver_path}")
                service = ChromeService(executable_path=driver_path)
                driver = webdriver.Chrome(service=service, options=options)
                driver.implicitly_wait(5)
                logger.info("✅ Chrome started via webdriver-manager fallback.")
                return driver
            except Exception as e2:
                logger.error(f"❌ webdriver-manager fallback failed: {e2}")
                raise

    def wait_for_page_ready(self, driver, timeout=20):
        try:
            WebDriverWait(driver, timeout).until(
                lambda d: d.execute_script("return document.readyState") in ["interactive", "complete"]
            )
            try:
                spa_needs_wait = driver.execute_script('''
                    return (window.React || window.Vue || window.angular || window.ng) && 
                           document.body.children.length <= 2;
                ''')
                if spa_needs_wait:
                    time.sleep(0.5)  # Reduced from 1
            except:
                pass
            time.sleep(Config.PAGE_EXTRA_WAIT)
            return True
        except TimeoutException:
            logger.warning("⚠️ Page did not become ready within timeout.")
            return False
        except Exception as e:
            logger.warning(f"⚠️ Page ready check failed: {e}")
            return False

    def get_real_browser_timings(self, driver):
        try:
            perf = driver.execute_script("""
                var timing = performance.timing;
                var navigation = performance.getEntriesByType('navigation')[0];
                return {
                    domContentLoaded: (timing.domContentLoadedEventEnd - timing.navigationStart) / 1000,
                    fullyLoaded: (timing.loadEventEnd - timing.navigationStart) / 1000,
                    firstPaint: navigation ? navigation.loadEventEnd / 1000 : 0,
                    domInteractive: (timing.domInteractive - timing.navigationStart) / 1000
                };
            """)
            return perf
        except:
            return None

    def enhanced_load_measurement(self, driver, url):
        start = time.time()
        driver.get(url)

        visual_load = None
        try:
            WebDriverWait(driver, 6).until(  # Reduced from 8
                EC.any_of(
                    EC.presence_of_element_located((By.CSS_SELECTOR, "h1, h2, img, .header, main, .content")),
                    EC.element_to_be_clickable((By.TAG_NAME, "a"))
                )
            )
            visual_load = round(time.time() - start, 2)
        except:
            pass

        interactive_load = None
        try:
            WebDriverWait(driver, 10).until(  # Reduced from 12
                EC.element_to_be_clickable((By.TAG_NAME, "body"))
            )
            interactive_load = round(time.time() - start, 2)
        except:
            pass

        self.wait_for_page_ready(driver, 15)  # Reduced from 20
        complete_load = round(time.time() - start, 2)

        browser_timing = self.get_real_browser_timings(driver)

        if browser_timing and browser_timing.get('domContentLoaded', 0) > 0.1:
            report_time = browser_timing['domContentLoaded']
        elif visual_load and visual_load < 8:  # Increased threshold
            report_time = visual_load
        elif interactive_load and interactive_load < 12:  # Increased threshold
            report_time = interactive_load
        else:
            report_time = complete_load * 0.75

        return round(report_time, 2)

    def get_body_text_and_log(self, driver, site_name, purpose="Main Page"):
        try:
            WebDriverWait(driver, 15).until(EC.presence_of_element_located((By.TAG_NAME, "body")))  # Reduced from 20
            time.sleep(0.5)  # Reduced from 1
            body = driver.find_element(By.TAG_NAME, "body")
            text = body.text.strip()
            if not text:
                iframes = driver.find_elements(By.TAG_NAME, "iframe")
                for iframe in iframes:
                    try:
                        driver.switch_to.frame(iframe)
                        iframe_body = driver.find_element(By.TAG_NAME, "body")
                        iframe_text = iframe_body.text.strip()
                        if iframe_text:
                            text = iframe_text
                            driver.switch_to.default_content()
                            break
                        driver.switch_to.default_content()
                    except Exception as e:
                        logger.warning(f"⚠️ Failed to get text from iframe: {e}")
                        driver.switch_to.default_content()
                else:
                    text = driver.execute_script("return document.body.innerText || document.body.textContent || '';").strip()
                    driver.switch_to.default_content()
            logger.info(f"[{site_name}] [{purpose}] Body text length={len(text)}; snippet={repr(text)[:100]}")
            return text
        except Exception as e:
            logger.warning(f"Could not get body text: {e}")
            return ""

    def check_status_code(self, url):
        try:
            r = requests.get(url, timeout=Config.HTTP_REQUEST_TIMEOUT)
            return r.status_code, None
        except (requests.exceptions.Timeout, requests.exceptions.ConnectionError) as e:
            logger.warning(f"⚠️ HTTP connectivity issue for {url}: {e}")
            return None, f"Connection error: {e.__class__.__name__}"
        except requests.exceptions.SSLError as e:
            logger.error(f"❌ SSL Error for {url}: {e}")
            return None, f"SSL Error: {e}"
        except Exception as e:
            logger.error(f"⚠️ HTTP request failed for {url}: {e}")
            return None, f"HTTP Request Error: {e}"

    def check_for_error_indicators(self, driver, site_name, purpose="Main Page"):
        try:
            title = _norm(driver.title)
            body_text = _norm(self.get_body_text_and_log(driver, site_name, purpose))
            error_phrases = [
                "page not found", "http 404", "not available",
                "something went wrong", "error 404", "temporarily unavailable",
                "cannot load", "this site can't be reached",
                "502 bad gateway", "503 service unavailable", "internal server error",
                "access denied", "under maintenance", "currently under maintenance",
                "site under maintenance", "proxy error", "blocked by administrator",
                "content blocked", "err_quic_protocol_error", "dns_probe_finished",
                "err_connection_timed_out", "err_connection_reset",
            ]
            for phrase in error_phrases:
                if phrase == "not available":
                    if phrase in title:
                        return phrase
                    if phrase in body_text and len(body_text) < 500:
                        return phrase
                else:
                    if phrase in title or phrase in body_text:
                        return phrase
            if len(body_text) < Config.SUSPECT_BODY_LENGTH:
                return "empty or incomplete page body"
        except Exception as e:
            logger.warning(f"⚠️ Error checking page indicators: {e}")
            return "error-check-failure"
        return None

    # ---------- SCREENSHOTS ----------
    def _build_screenshot_filename(self, site, tab, status, variant=None):
        site_s, tab_s = self._slug(site), self._slug(tab)
        var_s = self._slug(variant or "root")
        ts_ms = self._utc_stamp_ms()
        return f"{ts_ms}__{site_s}__{var_s}__{tab_s}__{status}.png"

    def capture_screenshot_simple(self, driver, site, tab, status, variant=None):
        key = (site, tab, (variant or "root"), status)
        # Reuse existing shot if we already took one this run
        prev = self._shot_index.get(key)
        if prev and os.path.exists(prev):
            logger.info(f"📸 Reusing existing screenshot for {key}: {prev}")
            return prev

        filename = self._build_screenshot_filename(site, tab, status, variant=variant)
        path = os.path.join(self.screenshot_dir, filename)
        try:
            driver.save_screenshot(path)
            logger.info(f"📸 Screenshot saved ({status}): {path}")
            self._shot_index[key] = path                      # track every status
            if status == 'FAILED':
                self.failure_screenshots[(site, tab, variant or "root")] = path
            return path
        except Exception as e:
            logger.warning(f"⚠️ Failed to save screenshot: {e}")
            return None


    def capture_screenshot_smart(self, driver, site, tab, status, variant=None):
        return self.capture_screenshot_simple(driver, site, tab, status, variant=variant)

    def capture_screenshot_for_failure(self, driver, site, tab, status="FAILED", variant=None):
        return self.capture_screenshot_simple(driver, site, tab, "FAILED", variant=variant)

    def capture_screenshot(self, driver, site, tab, variant=None):
        return self.capture_screenshot_simple(driver, site, tab, "SUCCESS", variant=variant)

    # ---------- ENHANCED VISUAL CHECK ----------
    def enhanced_visual_check(self, driver, screenshot_path=None):
        try:
            result = driver.execute_script('''
                var score = 0;
                var links = document.links.length;
                var buttons = document.querySelectorAll('button, .btn, input[type="submit"], input[type="button"]').length;
                var forms = document.forms.length;
                var headings = document.querySelectorAll('h1,h2,h3,h4').length;
                var textLen = document.body.innerText.length;
                var images = document.images.length;
                
                // Enhanced scoring for VM reliability
                if (links + buttons + forms > 5) score += 3;
                else if (links + buttons + forms > 2) score += 2;
                else if (links + buttons + forms > 0) score += 1;
                
                if (headings > 2) score += 2;
                else if (headings > 0) score += 1;
                
                if (textLen > 500) score += 3;
                else if (textLen > 100) score += 2;
                else if (textLen > 20) score += 1;
                
                if (images > 3) score += 1;
                
                // Check for interactive elements
                var interactive = document.querySelectorAll('nav, menu, .menu, .nav, [role="navigation"]').length;
                if (interactive > 0) score += 1;
                
                return score;
            ''')
            
            if screenshot_path and os.path.exists(screenshot_path):
                if self.is_screenshot_visually_rich(screenshot_path):
                    result += 2
                    
            return {'visual_score': result}
        except Exception as e:
            logger.warning(f"Enhanced visual check failed: {e}")
            return {'visual_score': 1}

    def hover_and_find_tab_link(self, driver, tab_name, parent_tab_name=None):
        try:
            actions = ActionChains(driver)
            if parent_tab_name:
                parent_xpath = f"//a[contains(translate(text(), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), '{parent_tab_name.lower()}')]"
                parent_tab = driver.find_element(By.XPATH, parent_xpath)
                actions.move_to_element(parent_tab).perform()
                time.sleep(0.5)  # Reduced from 1
            tab_xpath = f"//a[contains(translate(text(), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), '{tab_name.lower()}')]"
            return driver.find_element(By.XPATH, tab_xpath)
        except NoSuchElementException:
            logger.warning(f"⚠️ Tab '{tab_name}' with parent '{parent_tab_name}' not found.")
            return None
        except Exception as e:
            logger.warning(f"⚠️ Error finding tab '{tab_name}': {e}")
            return None

    def is_screenshot_visually_rich(self, path, color_variance_threshold=None):
        if color_variance_threshold is None:
            color_variance_threshold = Config.COLOR_VARIANCE_THRESHOLD
        try:
            img = Image.open(path).convert("RGB")
            data = np.array(img)
            std_dev = np.std(data, axis=(0, 1))
            mean_std = np.mean(std_dev)
            logger.info(f"Visual richness check: mean_std={mean_std:.2f}")
            return mean_std > color_variance_threshold
        except Exception as e:
            logger.warning(f"⚠️ Visual-rich check failed: {e}")
            return False

    def _is_white_background(self, driver, site_name):
        try:
            body_bg = driver.execute_script("return window.getComputedStyle(document.body).backgroundColor;")
            html_bg = driver.execute_script("return window.getComputedStyle(document.documentElement).backgroundColor;")
            logger.info(f"{site_name} background colors - body: {body_bg}, html: {html_bg}")
            def is_whiteish(bg):
                if not bg:
                    return False
                bg = bg.lower()
                if bg in ["white", "#ffffff"]:
                    return True
                m = re.match(r"rgb(a)?\(([^)]+)\)", bg)
                if m:
                    parts = [float(x.strip()) for x in m.group(2).split(",")]
                    if len(parts) == 4 and parts[3] == 0:
                        return True
                    if parts[0] >= 250 and parts[1] >= 250 and parts[2] >= 250:
                        return True
                return False
            return is_whiteish(body_bg) or is_whiteish(html_bg)
        except Exception as e:
            logger.warning(f"⚠️ Error checking white background: {e}")
            return False

    def is_screenshot_completely_white(self, path, threshold=0.99):
        try:
            img = Image.open(path).convert("RGB")
            data = np.array(img)
            white_pixels = np.all(data >= 250, axis=2)
            white_fraction = white_pixels.mean()
            logger.info(f"White pixel fraction: {white_fraction:.4f}")
            return white_fraction >= threshold
        except Exception as e:
            logger.warning(f"⚠️ Screenshot whiteness check failed: {e}")
            return False

    def _apply_special_site_exceptions(self, driver, url, site_name, tab_name, is_failure):
        # Only treat explicit special cases here. Do NOT flip 429 to success globally.
        # 429 handling is done by normal logic and the EXCEPTION_URLS blocks elsewhere.
        if "menlo" in driver.current_url.lower():
            return "SUCCESS", f"✅ Redirect to Menlo detected: {driver.current_url.lower()}"
        return None, None


    def should_retry_vm_aware(self, site_result, attempt):
        """Enhanced VM-aware retry logic"""
        if attempt >= Config.MAX_RETRIES:
            return False
            
        # Don't retry permanent failures
        permanent_errors = ['404', 'SSL Error', 'DNS Error', 'HTTP 403', 'HTTP 401', 'HTTP 410']
        msg = site_result.get('tabs', [{}])[0].get('message', '') if site_result.get('tabs') else ''
        if any(p in msg for p in permanent_errors):
            logger.info(f"🚫 Not retrying permanent error: {msg}")
            return False
        
        # VM-specific transient issues that should be retried
        vm_transient = [
            'timeout', 'connection', '502', '503', '429', 'crash',
            'memory', 'resource temporarily unavailable', 'chrome not reachable',
            'session not created', 'unable to obtain driver', 'chrome failed to start',
            'browser network error', 'err_connection', 'err_timed_out'
        ]
        
        should_retry = any(t in msg.lower() for t in vm_transient)
        
        # Also retry if load time is very high (might be temporary VM performance issue)
        load_time = site_result.get('site_load_time', 0)
        if load_time > Config.CRITICAL_THRESHOLD:
            should_retry = True
            logger.info(f"🔄 Retrying due to critical load time: {load_time}s")
        
        if should_retry:
            logger.info(f"🔄 Will retry VM-related issue: {msg}")
        else:
            logger.info(f"🚫 Not retrying non-VM issue: {msg}")
            
        return should_retry

    def click_and_verify_tab(self, driver, tab_name, tabdata, site_name, site_id, site_host, region_hint, pub_suffix):
        expected_url = None
        parent_tab = None
        if isinstance(tabdata, dict):
            expected_url = tabdata.get("url")
            parent_tab = tabdata.get("parent") or None
        else:
            expected_url = tabdata

        result = {'tab': tab_name, 'expected_url': expected_url, 'status': 'UNKNOWN',
                  'message': '', 'url': None, 'load_time': 0, 'variant': None}
        parent_window = driver.current_window_handle

        def curr_variant():
            try:
                return self._url_variant(driver.current_url)
            except Exception:
                return "root"

        try:
            # DIRECT URL
            if expected_url:
                driver.execute_script("window.open(arguments[0], '_blank');", expected_url)
                driver.switch_to.window(driver.window_handles[-1])

                t0 = time.time()
                self.wait_for_page_ready(driver, Config.TAB_LOAD_TIMEOUT)
                time.sleep(Config.PAGE_EXTRA_WAIT)
                load_time = round(time.time() - t0, 2)  # <-- FIX: define before use

                result['load_time'] = load_time
                result['url'] = driver.current_url
                result['variant'] = self._url_variant(result['url'])

                neterr, errcode = detect_chrome_net_error(driver)
                if neterr:
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=f"❌ Browser network error ({errcode})", screenshot=p)
                    # audit_tab auto-adds VM-normalized fields
                    self.audit_tab(
                        site_id=site_id, site_name=site_name, site_host=site_host,
                        region_hint=region_hint, public_suffix=pub_suffix,
                        tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                        expected_url=result.get("expected_url"), actual_url=result.get("url"),
                        error_message=result.get("message")
                    )
                                   
                    driver.close(); driver.switch_to.window(parent_window)
                    return result

                if is_exception_site(result['url']):
                    code, err = self.check_status_code(driver.current_url)
                    if code == 429 or (code is not None and 200 <= code < 400):
                        p = self.capture_screenshot_simple(driver, site_name, tab_name, "SUCCESS", variant=result['variant'])
                        result.update(status="SUCCESS", message="Exception site: 429 or successful HTTP status treated as success", screenshot=p)
                        self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                       region_hint=region_hint, public_suffix=pub_suffix,
                                       tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                       expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                       error_message=result.get("message"))
                        driver.close(); driver.switch_to.window(parent_window)
                        return result
                    elif code is not None and code >= 400:
                        p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                        result.update(status="FAILED", message=f"Exception site: HTTP error {code}", screenshot=p)
                        self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                       region_hint=region_hint, public_suffix=pub_suffix,
                                       tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                       expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                       error_message=result.get("message"))
                        driver.close(); driver.switch_to.window(parent_window)
                        return result
                    elif err:
                        p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                        result.update(status="FAILED", message=f"Exception site: Network error {err}", screenshot=p)
                        self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                       region_hint=region_hint, public_suffix=pub_suffix,
                                       tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                       expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                       error_message=result.get("message"))
                        driver.close(); driver.switch_to.window(parent_window)
                        return result

                special_status, special_msg = self._apply_special_site_exceptions(driver, driver.current_url, site_name, tab_name, False)
                if special_status == "SUCCESS":
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "SUCCESS", variant=result['variant'])
                    result.update(status=special_status, message=special_msg, screenshot=p)
                    self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                   region_hint=region_hint, public_suffix=pub_suffix,
                                   tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                   expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                   error_message=result.get("message"))
                    driver.close(); driver.switch_to.window(parent_window)
                    return result
                elif special_status == "FAILED":
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=special_msg, screenshot=p)
                    self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                   region_hint=region_hint, public_suffix=pub_suffix,
                                   tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                   expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                   error_message=result.get("message"))
                    driver.close(); driver.switch_to.window(parent_window)
                    return result

                status_code, error_msg = self.check_status_code(driver.current_url)
                if (status_code is not None and status_code >= 400):
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=f"❌ Tab Error: HTTP Status {status_code}", screenshot=p)
                    self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                   region_hint=region_hint, public_suffix=pub_suffix,
                                   tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                   expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                   error_message=result.get("message"))
                    driver.close(); driver.switch_to.window(parent_window)
                    return result
                elif error_msg and not any(t in _norm(error_msg) for t in ["connection error", "timeout"]):
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=f"❌ Tab Error: {error_msg}", screenshot=p)
                    self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                   region_hint=region_hint, public_suffix=pub_suffix,
                                   tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                   expected_url=result.get("expected_url"), actual_url=result.get("url"),
                                   error_message=result.get("message"))
                    driver.close(); driver.switch_to.window(parent_window)
                    return result

                error = self.check_for_error_indicators(driver, site_name, tab_name)
                if error and not is_exception_site(driver.current_url):
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=f"❌ ERROR PAGE: {tab_name} → {result['url']} (keyword: '{error}')", screenshot=p)
                else:
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "SUCCESS", variant=result['variant'])
                    result.update(status="SUCCESS", message=f"✅ {tab_name} → {result['url']} ({load_time}s)", screenshot=p)

                self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                               region_hint=region_hint, public_suffix=pub_suffix,
                               tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                               expected_url=result.get("expected_url"), actual_url=result.get("url"),
                               error_message=result.get("message"))
                driver.close(); driver.switch_to.window(parent_window)
                return result

            # MENU CLICK
            else:
                tab_element = self.hover_and_find_tab_link(driver, tab_name, parent_tab=None)
                if not tab_element:
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=curr_variant())
                    result.update(status="FAILED", message=f"❌ Tab '{tab_name}' not found", screenshot=p, variant=curr_variant())
                    self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                   region_hint=region_hint, public_suffix=pub_suffix,
                                   tab=tab_name, attempt=1, status=result['status'], error_message=result.get("message"))
                    return result

                t0 = time.time()
                tab_element.click()
                self.wait_for_page_ready(driver, Config.TAB_LOAD_TIMEOUT)
                time.sleep(Config.PAGE_EXTRA_WAIT)
                load_time = round(time.time() - t0, 2)

                current_url = driver.current_url
                result['load_time'] = load_time
                result['url'] = current_url
                result['variant'] = self._url_variant(current_url)

                neterr, errcode = detect_chrome_net_error(driver)
                if neterr:
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=f"❌ Browser network error ({errcode})", screenshot=p)
                    self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                   region_hint=region_hint, public_suffix=pub_suffix,
                                   tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                   actual_url=current_url, expected_url=result.get("expected_url"),
                                   error_message=result.get("message"))
                    return result

                if is_exception_site(current_url):
                    code, err = self.check_status_code(current_url)
                    if code == 429 or (code is not None and 200 <= code < 400):
                        p = self.capture_screenshot_simple(driver, site_name, tab_name, "SUCCESS", variant=result['variant'])
                        result.update(status="SUCCESS", message="Exception site tab: 429 or successful HTTP status treated as success", screenshot=p)
                        self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                       region_hint=region_hint, public_suffix=pub_suffix,
                                       tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                       actual_url=current_url, expected_url=result.get("expected_url"))
                        return result
                    elif code is not None and code >= 400:
                        p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                        result.update(status="FAILED", message=f"Exception site tab: HTTP error {code}", screenshot=p)
                        self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                       region_hint=region_hint, public_suffix=pub_suffix,
                                       tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                       actual_url=current_url, expected_url=result.get("expected_url"),
                                       error_message=result.get("message"))
                        return result
                    elif err:
                        p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                        result.update(status="FAILED", message=f"Exception site tab: Network error {err}", screenshot=p)
                        self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                                       region_hint=region_hint, public_suffix=pub_suffix,
                                       tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                                       actual_url=current_url, expected_url=result.get("expected_url"),
                                       error_message=result.get("message"))
                        return result

                error = self.check_for_error_indicators(driver, site_name, tab_name)
                if error and not is_exception_site(current_url):
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=result['variant'])
                    result.update(status="FAILED", message=f"❌ ERROR PAGE: {tab_name} → {current_url} (keyword: '{error}')", screenshot=p)
                else:
                    p = self.capture_screenshot_simple(driver, site_name, tab_name, "SUCCESS", variant=result['variant'])
                    result.update(status="SUCCESS", message=f"✅ {tab_name} → {current_url} ({load_time}s)", screenshot=p)

                self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                               region_hint=region_hint, public_suffix=pub_suffix,
                               tab=tab_name, attempt=1, status=result['status'], load_time_s=load_time,
                               actual_url=current_url, expected_url=result.get("expected_url"),
                               error_message=result.get("message"))
                return result

        except Exception as e:
            try:
                if len(driver.window_handles) > 1:
                    driver.close()
                    driver.switch_to.window(parent_window)
            except Exception:
                pass
            v = curr_variant()
            p = self.capture_screenshot_simple(driver, site_name, tab_name, "FAILED", variant=v)
            result.update(status="FAILED", message=f"❌ {tab_name} failed: {str(e).splitlines()[0]}", screenshot=p, variant=v)
            self.audit_tab(site_id=site_id, site_name=site_name, site_host=site_host,
                           region_hint=region_hint, public_suffix=pub_suffix,
                           tab=tab_name, attempt=1, status=result['status'], load_time_s=result.get("load_time"),
                           expected_url=result.get("expected_url"), actual_url=result.get("url"),
                           error_message=result.get("message"))
            return result

    # ------------ NEW: MERGE MAIN PAGE STATUS TO AVOID DUPLICATE SCREENSHOTS ------------
    def _merge_mainpage_status(self, site, status_label, msg, load_time, variant):
        """
        Upgrade/annotate the existing 'Main Page' row instead of appending a new one.
        Keeps the original screenshot; just bumps status/message.
        """
        main_row = next((t for t in site['tabs'] if t.get('tab') == "Main Page"), None)
        if not main_row:
            site['tabs'].append({
                'tab': "Main Page", 'status': status_label, 'message': msg,
                'load_time': load_time, 'variant': variant
            })
            return
        rank = {"SUCCESS": 1, "SLOW": 2, "WARNING": 2, "FAILED": 3}
        cur = (main_row.get("status") or "SUCCESS").upper()
        if rank.get(status_label, 0) > rank.get(cur, 0):
            main_row["status"] = status_label
        existing = main_row.get("message", "")
        if msg and msg not in existing:
            main_row["message"] = f"{existing} | {msg}" if existing else msg
        main_row["load_time"] = load_time
        if not main_row.get("variant"):
            main_row["variant"] = variant  # do not touch screenshot

    # ---------- ENHANCED SITE LOGIC ----------
    def monitor_site(self, name, data):
        logger.info(f"🔎 Monitoring site: {name}")
        domain = urlparse(data['base_url']).netloc.lower()
        if domain.startswith("www."):
            domain = domain[4:]
        skip_retry = domain in Config.SLOW_ALERT_WHITELIST
        attempt = 0

        # Keep original per-row key as site_id (so dashboard counts don't collapse)
        site_id = name
        site_host = canonical_host(data['base_url'])
        region_hint = region_hint_from_host(site_host)
        pub_suffix = public_suffix_simple(site_host)

        def single_run():
            site = {
                'site_id': site_id,                # original key (unchanged dashboard behavior)
                'site_host': site_host,            # new: canonical host
                'region_hint': region_hint,        # new: e.g., NL
                'public_suffix': pub_suffix,       # new: e.g., com.nl / nl
                'site_name': data.get("site_name", name),
                'base_url': data['base_url'],
                'tabs': [],
                'status': 'UNKNOWN',
                'site_load_time': 0,
            }
            variant = self._url_variant(data['base_url'])
            driver = None
            try:
                driver = self.create_driver()

                self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                tab="Main Page", attempt=attempt + 1, status="START")

                site['site_load_time'] = self.enhanced_load_measurement(driver, data['base_url'])
                # VM-normalized (so dashboards/SLO use environment-agnostic timing)
                site['site_load_time_vm_norm'] = round(
                    site['site_load_time'] / max(1.0, Config.VM_PERFORMANCE_FACTOR), 2
                )

                neterr, errcode = detect_chrome_net_error(driver)
                if neterr:
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                    site['status'] = "FAILED"
                    msg = f"❌ Browser network error detected ({errcode})"
                    site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': msg, 'screenshot': p, 'variant': variant})
                    self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                    site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                    tab="Main Page", attempt=attempt + 1, status=site['status'],
                                    load_time_s=site['site_load_time'], error_message=msg)
                    return site

                # LOADED audit; auto helper will include vm fields (we also pass explicitly — harmless)
                self.audit_site(
                    site_id=site_id,
                    site_name=site['site_name'],
                    base_url=site['base_url'],
                    site_host=site_host,
                    region_hint=region_hint,
                    public_suffix=pub_suffix,
                    tab="Main Page",
                    attempt=attempt + 1,
                    status="LOADED",
                    load_time_s=site['site_load_time'],
                    load_time_vm_norm_s=site['site_load_time_vm_norm'],
                    vm_factor=Config.VM_PERFORMANCE_FACTOR
                )               

                if is_exception_site(data['base_url']):
                    code, err = self.check_status_code(data['base_url'])
                    if code == 429 or (code is not None and 200 <= code < 400):
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "SUCCESS", variant=variant)
                        site['status'] = "SUCCESS"
                        msg = "Exception site: HTTP 429 or HTTP 2xx/3xx accepted as success"
                        site['tabs'].append({'tab': "Main Page", 'status': "SUCCESS", 'message': msg, 'screenshot': p, 'variant': variant})
                        self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                        site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                        tab="Main Page", attempt=attempt + 1, status=site['status'],
                                        http_status=code, error_message=msg)
                        return site
                    elif code is not None and code >= 400:
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                        site['status'] = "FAILED"
                        msg = f"Exception site: HTTP error {code}"
                        site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': msg, 'screenshot': p, 'variant': variant})
                        self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                        site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                        tab="Main Page", attempt=attempt + 1, status=site['status'],
                                        http_status=code, error_message=msg)
                        return site
                    elif err:
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                        site['status'] = "FAILED"
                        msg = f"Exception site: Network error {err}"
                        site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': msg, 'screenshot': p, 'variant': variant})
                        self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                        site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                        tab="Main Page", attempt=attempt + 1, status=site['status'],
                                        error_message=msg)
                        return site

                special_status, special_msg = self._apply_special_site_exceptions(driver, data['base_url'], site['site_name'], "Main Page", False)
                if special_status == "SUCCESS":
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "SUCCESS", variant=variant)
                    site['status'] = special_status
                    site['tabs'].append({'tab': "Main Page", 'status': special_status, 'message': special_msg, 'screenshot': p, 'variant': variant})
                    self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                    site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                    tab="Main Page", attempt=attempt + 1, status=site['status'],
                                    error_message=special_msg)
                    return site
                elif special_status == "FAILED":
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                    site['status'] = "FAILED"
                    site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': special_msg, 'screenshot': p, 'variant': variant})
                    self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                    site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                    tab="Main Page", attempt=attempt + 1, status=site['status'],
                                    error_message=special_msg)
                    return site

                status_code, error_msg = self.check_status_code(data['base_url'])
                if (status_code is not None and status_code >= 400):
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                    site['status'] = "FAILED"
                    msg = f"❌ Site Error: HTTP Status {status_code}"
                    site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': msg, 'screenshot': p, 'variant': variant})
                    self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                    site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                    tab="Main Page", attempt=attempt + 1, status=site['status'],
                                    http_status=status_code, error_message=msg)
                    return site
                elif error_msg and not any(t in _norm(error_msg) for t in ["connection error", "timeout"]):
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                    site['status'] = "FAILED"
                    msg = f"❌ Site Error: {error_msg}"
                    site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': msg, 'screenshot': p, 'variant': variant})
                    self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                    site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                    tab="Main Page", attempt=attempt + 1, status=site['status'],
                                    error_message=msg)
                    return site

                # Enhanced analysis with improved warning logic
                keyword = self.check_for_error_indicators(driver, site['site_name'], "Main Page")
                visual_checks = self.enhanced_visual_check(driver)

                if keyword and keyword != "empty or incomplete page body":
                    site['status'] = "FAILED"
                    msg = f"❌ ERROR PAGE (Keyword: '{keyword}')"
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                else:
                    score = visual_checks['visual_score']
                    
                    if score >= 7:  # Excellent functionality
                        site['status'] = "SUCCESS"
                        msg = f"✅ Site fully functional (score: {score}/9+)"
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "SUCCESS", variant=variant)
                    elif score >= 5:  # Good functionality
                        site['status'] = "SUCCESS" 
                        msg = f"✅ Site functional (score: {score}/9+)"
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "SUCCESS", variant=variant)
                    elif score >= 3:  # Limited but acceptable
                        site['status'] = "WARNING"
                        msg = f"⚠️ Limited functionality (score: {score}/9+)"
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "WARNING", variant=variant)
                    elif keyword == "empty or incomplete page body" and score >= 2:
                        site['status'] = "WARNING"
                        msg = f"⚠️ Minimal content detected (score: {score}/9+)"
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "WARNING", variant=variant)
                    else:
                        site['status'] = "FAILED"
                        msg = f"❌ Poor functionality (score: {score}/9+)"
                        p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)

                site['tabs'].append({'tab': "Main Page", 'status': site['status'], 'message': msg, 'screenshot': p, 'variant': variant})
                self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                tab="Main Page", attempt=attempt + 1, status=site['status'],
                                load_time_s=site['site_load_time'], error_message=msg, 
                                visual_score=visual_checks['visual_score'])

                # --------- Enhanced SLOW flags with VM awareness (MERGED; no duplicate rows) ---------
                is_whitelisted = is_slow_whitelisted(data['base_url'])
                if not is_whitelisted:
                    if site['site_load_time'] > Config.CRITICAL_THRESHOLD:
                        self._merge_mainpage_status(
                            site, "FAILED",
                            f"❌ CRITICAL slow ({site['site_load_time']:.1f}s)",
                            site['site_load_time'], variant
                        )
                        site['status'] = "FAILED"
                    elif site['site_load_time'] > Config.VERY_SLOW_THRESHOLD:
                        self._merge_mainpage_status(
                            site, "SLOW",
                            f"⚠️ VERY slow ({site['site_load_time']:.1f}s)",
                            site['site_load_time'], variant
                        )
                    elif site['site_load_time'] > Config.SLOW_THRESHOLD:
                        self._merge_mainpage_status(
                            site, "SLOW",
                            f"⚠️ Slow ({site['site_load_time']:.1f}s)",
                            site['site_load_time'], variant
                        )

                # TABS
                tabs = data.get("tabs")
                if tabs and isinstance(tabs, dict) and len(tabs) > 0:
                    for tab_name, tab_data in tabs.items():
                        try:
                            driver.get(data['base_url'])
                            time.sleep(1)  # Reduced from 2
                            tab_result = self.click_and_verify_tab(
                                driver, tab_name, tab_data, site['site_name'],
                                site_id, site_host, region_hint, pub_suffix
                            )
                            site['tabs'].append(tab_result)
                            if tab_result['status'] == "FAILED" and site['status'] not in ["FAILED", "WARNING"]:
                                site['status'] = "WARNING"
                        except Exception as e:
                            logger.error(f"❌ Exception during tab check {tab_name}: {e}")
                            p = None
                            try:
                                p = self.capture_screenshot_simple(driver, site['site_name'], tab_name, "FAILED", variant=variant)
                            except:
                                pass
                            site['tabs'].append({
                                'tab': tab_name,
                                'status': "FAILED",
                                'message': f"❌ Exception during tab check: {str(e).splitlines()[0]}",
                                'screenshot': p,
                                'variant': variant
                            })
                            self.audit_tab(site_id=site_id, site_name=site['site_name'], site_host=site_host,
                                           region_hint=region_hint, public_suffix=pub_suffix,
                                           tab=tab_name, attempt=1, status="FAILED", error_message=str(e).splitlines()[0])
                            if site['status'] not in ["FAILED", "WARNING"]:
                                site['status'] = "WARNING"

                return site

            except Exception as e:
                logger.error(f"❌ Exception during site monitoring {name}: {e}")
                p = None
                try:
                    p = self.capture_screenshot_simple(driver, site['site_name'], "Main Page", "FAILED", variant=variant)
                except:
                    pass
                site['status'] = "FAILED"
                site['tabs'].append({'tab': "Main Page", 'status': "FAILED", 'message': f"❌ Site crash: {str(e).splitlines()[0]}", 'screenshot': p, 'variant': variant})
                self.audit_site(site_id=site_id, site_name=site['site_name'], base_url=site['base_url'],
                                site_host=site_host, region_hint=region_hint, public_suffix=pub_suffix,
                                tab="Main Page", attempt=attempt + 1, status="FAILED",
                                error_message=str(e).splitlines()[0])
                return site
            finally:
                if driver:
                    driver.quit()

        site_result = single_run()
        attempt += 1

        # Enhanced retry logic using VM-aware method
        while attempt <= Config.MAX_RETRIES and self.should_retry_vm_aware(site_result, attempt) and not skip_retry:
            logger.info(f"🔁 Retrying site '{name}' (attempt {attempt + 1}/{Config.MAX_RETRIES + 1})")
            audit.write({"event": "retry", "site_id": site_id, "site_name": data.get("site_name", name),
                         "base_url": data["base_url"], "site_host": site_host,
                         "region_hint": region_hint, "public_suffix": pub_suffix,
                         "attempt": attempt + 1, "reason": "vm_aware_retry"})
            time.sleep(Config.RETRY_DELAY_SECONDS)
            site_result_retry = single_run()

            def better(new, old):
                pri = {'SUCCESS': 3, 'WARNING': 2, 'FAILED': 1, 'UNKNOWN': 0}
                return pri.get(new.get('status', 'UNKNOWN'), 0) > pri.get(old.get('status', 'UNKNOWN'), 0)

            if better(site_result_retry, site_result):
                site_result = site_result_retry
                logger.info(f"✅ Retry improved result for '{name}': {site_result.get('status')}")
                break
            else:
                site_result = site_result_retry
                attempt += 1

        return site_result

    # ---------- EMAIL ATTACHMENTS ----------
    def build_failure_attachments(self, issues_filtered):
        def find_latest_by_pattern(site_display, tab_name, variant=None):
            ss, tt = self._slug(site_display), self._slug(tab_name)
            vv = self._slug(variant or "root")
            best = None; best_mtime = -1
            try:
                for fn in os.listdir(self.screenshot_dir):
                    if "__FAILED__" not in fn:
                        continue
                    blob = fn.lower()
                    if ss.lower() in blob and tt.lower() in blob and vv.lower() in blob:
                        full = os.path.join(self.screenshot_dir, fn)
                        m = os.path.getmtime(full)
                        if m > best_mtime:
                            best, best_mtime = full, m
            except Exception:
                pass
            return best

        manifest, idx = [], 1
        for site in issues_filtered:
            site_display = site.get('site_name')
            site_id = site.get('site_id', site_display)
            for tab in site.get('tabs', []):
                if tab.get('status') not in ['FAILED', 'WARNING', 'SLOW']:  # Include WARNING screenshots
                    continue
                tab_name = tab.get('tab', '')
                variant = tab.get('variant') or "root"
                p = tab.get('screenshot')
                if not p:
                    p = (self.failure_screenshots.get((site_display, tab_name, variant))
                         or self.failure_screenshots.get((site_id, tab_name, variant)))
                if not p:
                    p = find_latest_by_pattern(site_display, tab_name, variant)
                if not p or not os.path.exists(p):
                    continue
                status_suffix = tab.get('status', 'FAILED')
                display_name = f"{idx:02d}__{self._slug(site_display)}__{self._slug(variant)}__{self._slug(tab_name)}__{status_suffix}__{self._utc_stamp()}.png"
                manifest.append({"path": p, "name": display_name, "site": site_display, "tab": tab_name, "message": tab.get('message', ''), "variant": variant})
                idx += 1

        seen, deduped = set(), []
        for item in manifest:
            if item["name"] not in seen:
                deduped.append(item)
                seen.add(item["name"])
        return deduped

    # ---------- ENHANCED RUN LOOP ----------
    def run_monitoring(self):
        # VM Health Check
        if not self.check_vm_health():
            logger.error("❌ VM resources critically low, aborting monitoring")
            audit.write({"event": "abort", "reason": "vm_resources_critical"})
            return
            
        # VM Performance Calibration
        logger.info("🔧 Starting VM performance calibration...")
        perf_factor = self.calibrate_vm_baseline()
        
        self.failure_screenshots = {}
        try:
            os.makedirs(self.screenshot_dir, exist_ok=True)
            for fn in os.listdir(self.screenshot_dir):
                fp = os.path.join(self.screenshot_dir, fn)
                if os.path.isfile(fp):
                    os.remove(fp)
            logger.info(f"🧹 Cleared previous screenshots in: {self.screenshot_dir}")
        except Exception as e:
            logger.warning(f"⚠️ Could not clear screenshots: {e}")

        update_json_from_excel(Config.EXCEL_PATH, Config.SITES_JSON)

        with open(Config.SITES_JSON, "r", encoding="utf-8") as f:
            sites = json.load(f)

        logger.info(f"📊 Loaded {len(sites)} sites for monitoring with VM factor {perf_factor:.1f}")
        audit.write({"event": "start", "total_sites": len(sites), "run_id": RUN_ID, 
                     "screenshot_dir": self.screenshot_dir, "vm_performance_factor": perf_factor,
                     "vm_baseline_time": Config.VM_BASELINE_TIME})

        results = []
        with ThreadPoolExecutor(max_workers=Config.MAX_WORKERS) as executor:
            futures = [executor.submit(self.monitor_site, name, data) for name, data in sites.items()]
            for future in as_completed(futures):
                try:
                    results.append(future.result())
                except Exception as e:
                    logger.error(f"❌ Exception in monitoring thread: {e}")

        issues = [site for site in results if any(tab.get('status') in ['FAILED', 'WARNING', 'SLOW'] for tab in site.get('tabs', []))]
        issues_filtered = []
        for site in issues:
            base_url = site.get('base_url', '')
            if is_slow_whitelisted(base_url):
                real_issues = [tab for tab in site['tabs'] if tab.get('status') in ['FAILED', 'WARNING']]
                if real_issues:
                    site['tabs'] = real_issues
                    issues_filtered.append(site)
            else:
                issues_filtered.append(site)

        if issues_filtered:
            logger.info(f"📣 Issues found in {len(issues_filtered)} site(s). Preparing email...")
            if Config.USE_HTML_EMAIL:
                manifest = self.build_failure_attachments(issues_filtered)
                body = self.generate_html_email(results_all=results, issues_only=issues_filtered)
                email_attachments = manifest
            else:
                body = self.generate_plain_report(issues_filtered)
                manifest = self.build_failure_attachments(issues_filtered)
                email_attachments = manifest

            # Enhanced subject with VM performance info
            vm_info = f" (VM: {perf_factor:.1f}x)" if perf_factor > 1.2 else ""
            subject = f"🔍 Enhanced Website Monitor Report{vm_info} – {datetime.now(IST).strftime('%Y-%m-%d %H:%M:%S')}"
            self.send_email(subject, body, html=Config.USE_HTML_EMAIL, attachments=email_attachments)
            audit.write({"event": "email", "status": "SENT", "attachments": [m.get("name") for m in manifest], "vm_factor": perf_factor})
        else:
            logger.info("✅ All sites healthy — no email sent.")

        self.save_excel(results)
        audit.write({"event": "excel", "file": Config.RESULTS_EXCEL})
        audit.write({"event": "end", "vm_performance_factor": perf_factor})
        self.cleanup_old_audit_logs(retention_days=8)

    def generate_plain_report(self, results):
        lines = [f"🔍 Enhanced Website Monitor Report – {datetime.now(IST).strftime('%Y-%m-%d %H:%M:%S')}"]
        lines.append(f"🖥️ VM Performance Factor: {Config.VM_PERFORMANCE_FACTOR:.1f}x")
        lines.append("")
        for site in results:
            lines.append(f"🟣 {site['site_name']} → {site['base_url']}")
            lines.append(f"⏱️ Load Time: {site['site_load_time']}s")
            for tab in site['tabs']:
                lines.append(f"   {tab.get('message')}")
            lines.append("")
        return "\n".join(lines)

    def generate_html_email(self, results_all, issues_only, manifest=None):
        ts_str = datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S")

        all_tabs = [t for s in results_all for t in s.get('tabs', [])]
        succ = sum(1 for t in all_tabs if (t.get('status') or '').upper() == 'SUCCESS')
        warn = sum(1 for t in all_tabs if (t.get('status') or '').upper() in ('WARNING', 'SLOW'))
        fail = sum(1 for t in all_tabs if (t.get('status') or '').upper() == 'FAILED')

        def status_color(status: str):
            st = (status or '').upper()
            if st == "SUCCESS":
                return "#22c55e"
            if st in ("WARNING", "SLOW"):
                return "#f59e0b"
            return "#ef4444"

        def status_icon(status: str):
            st = (status or '').upper()
            if st == "SUCCESS":
                return "✅"
            if st in ("WARNING", "SLOW"):
                return "⚠️"
            return "🚨"

        def generate_site_card(site):
            site_name = site.get('site_name')
            base_url = site.get('base_url')
            load_time = site.get('site_load_time_vm_norm', site.get('site_load_time', 0))

            worst_status = "SUCCESS"
            for tab in site.get('tabs', []):
                st = (tab.get('status') or '').upper()
                if st == "FAILED":
                    worst_status = "FAILED"; break
                if st in ("WARNING", "SLOW") and worst_status != "FAILED":
                    worst_status = "WARNING"

            if worst_status == "FAILED":
                border_color, bg_color, icon = "#ef4444", "#fef2f2", "🚨"
            elif worst_status == "WARNING":
                border_color, bg_color, icon = "#f59e0b", "#fffbeb", "⚠️"
            else:
                border_color, bg_color, icon = "#22c55e", "#f0fdf4", "✅"

            tab_details = ""
            for tab in site.get('tabs', []):
                msg = tab.get('message', '')
                st = tab.get('status', '')
                color = status_color(st)
                tab_icon = status_icon(st)
                tab_details += f"""
                <div style="margin:8px 0;padding:8px 12px;background:#ffffff;border-radius:6px;border-left:4px solid {color};">
                  <span style="font-weight:600;color:#111827;">{tab_icon} {tab.get('tab', 'Page')}</span>
                  <div style="font-size:13px;color:#374151;margin-top:2px;">{msg}</div>
                </div>"""

            return f"""
            <div style="background:{bg_color};border:2px solid {border_color};border-radius:12px;margin:16px 0;box-shadow:0 4px 12px rgba(0,0,0,0.08);overflow:hidden;">
              <div style="padding:18px 20px;background:#ffffff;border-bottom:2px solid {border_color};">
                <div style="display:flex;align-items:center;justify-content:space-between;">
                  <div style="flex:1;">
                    <div style="font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Arial,sans-serif;font-size:18px;font-weight:700;color:#111827;margin-bottom:4px;">
                      {icon} {site_name}
                    </div>
                    <div style="font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Arial,sans-serif;font-size:13px;color:#6b7280;">
                      <a href="{base_url}" style="color:#2563eb;text-decoration:none;font-weight:500;">{base_url}</a>
                    </div>
                  </div>
                  <div style="text-align:center;min-width:80px;">
                    <div style="background:{border_color};color:#ffffff;padding:6px 12px;border-radius:20px;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Arial,sans-serif;font-size:12px;font-weight:700;">
                      ⏱ {load_time:.1f}s
                    </div>
                  </div>
                </div>
              </div>
              <div style="padding:16px 20px;">
                {tab_details}
              </div>
            </div>"""

        # VM Performance indicator
        vm_indicator = ""
        if Config.VM_PERFORMANCE_FACTOR > 1.5:
            vm_indicator = f"""
            <div style="background:#fef3c7;border:2px solid #f59e0b;border-radius:8px;padding:12px;margin-bottom:16px;">
              <div style="font-size:13px;color:#92400e;font-weight:600;text-align:center;">
                🖥️ VM Performance Factor: {Config.VM_PERFORMANCE_FACTOR:.1f}x (Adjusted thresholds for VM environment)
              </div>
            </div>"""

        top_credit = f"""
        <table role="presentation" width="100%" cellpadding="0" cellspacing="0" style="border-collapse:collapse;">
          <tr>
            <td align="center" style="padding:8px 0;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Arial,sans-serif;font-size:12px;line-height:1.35;color:#374151;background-color:#f9fafb;border-bottom:1px solid #e5e7eb;">
              Developed by <strong style="color:#111827;font-weight:600;">Vishal Chauhan</strong> for SPACE • VM-Optimized Monitoring
            </td>
          </tr>
        </table>"""

        html = f"""
        <!DOCTYPE html>
        <html>
        <head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"></head>
        <body style="margin:0;padding:20px;background:#f5f5f5;font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Arial,sans-serif;">
          {top_credit}

          <table role="presentation" width="100%" cellpadding="0" cellspacing="0" style="border-collapse:collapse;max-width:800px;margin:0 auto;background:#ffffff;border-radius:12px;box-shadow:0 4px 20px rgba(0,0,0,0.08);overflow:hidden;">
            <tr>
              <td style="padding:28px 24px;background:#111827;color:#ffffff;text-align:center;">
                <div style="font-size:24px;font-weight:700;color:#ffffff;line-height:1.3;margin-bottom:8px;">
                  🔍 Enhanced Website Monitor Report
                </div>
                <div style="font-size:14px;color:#d1d5db;line-height:1.4;">
                  {ts_str} • VM-Optimized Real-time monitoring with intelligent analysis
                </div>
              </td>
            </tr>

            <tr>
              <td style="padding:24px;">
                {vm_indicator}
                
                <table role="presentation" width="100%" cellpadding="0" cellspacing="0" style="border-collapse:collapse;margin-bottom:24px;">
                  <tr>
                    <td style="width:25%;text-align:center;border:2px solid #22c55e;padding:16px;background:#f0fdf4;border-radius:8px;">
                      <div style="font-size:28px;font-weight:800;color:#15803d;">✅ {succ}</div>
                      <div style="font-size:12px;color:#6b7280;font-weight:600;text-transform:uppercase;margin-top:4px;">Success</div>
                    </td>
                    <td style="width:8%;"></td>
                    <td style="width:25%;text-align:center;border:2px solid #f59e0b;padding:16px;background:#fffbeb;border-radius:8px;">
                      <div style="font-size:28px;font-weight:800;color:#d97706;">⚠️ {warn}</div>
                      <div style="font-size:12px;color:#6b7280;font-weight:600;text-transform:uppercase;margin-top:4px;">Warning</div>
                    </td>
                    <td style="width:8%;"></td>
                    <td style="width:25%;text-align:center;border:2px solid #ef4444;padding:16px;background:#fef2f2;border-radius:8px;">
                      <div style="font-size:28px;font-weight:800;color:#dc2626;">🚨 {fail}</div>
                      <div style="font-size:12px;color:#6b7280;font-weight:600;text-transform:uppercase;margin-top:4px;">Failed</div>
                    </td>
                  </tr>
                </table>

                <div style="margin-top:16px;">
        """

        for site in issues_only:
            html += generate_site_card(site)

        html += f"""
                </div>

                <div style="background:#f8fafc;border:2px solid #e2e8f0;border-radius:8px;padding:16px;margin-top:24px;">
                  <div style="font-size:13px;color:#374151;font-weight:500;text-align:center;">
                    📎 Screenshots are attached for failed and warning monitoring checks
                  </div>
                </div>
              </td>
            </tr>

            <tr>
              <td style="background:#111827;color:#d1d5db;text-align:center;font-size:12px;padding:16px;">
                Report ID: {RUN_ID} | Generated: {ts_str} | VM Factor: {Config.VM_PERFORMANCE_FACTOR:.1f}x
              </td>
            </tr>
          </table>
        </body>
        </html>
        """
        return html

    def send_email(self, subject, body, html=False, attachments=None):
        try:
            send_email_graph(subject, body, html, attachments)
        except Exception as e:
            logger.error(f"❌ Email sending failed: {e}")

    def save_excel(self, results):
        rows = []
        for site in results:
            base_url = site.get('base_url', '')
            for tab in site.get('tabs', []):
                lt = tab.get('load_time') or 0.0
                vmn = round(lt / max(1.0, Config.VM_PERFORMANCE_FACTOR), 2) if isinstance(lt, (int, float)) else 0.0
                rows.append({
                    "timestamp": datetime.now().isoformat(),
                    "site": site.get('site_name'),
                    "site_id": site.get('site_id'),  # original key (dashboard-safe)
                    "site_host": site.get('site_host'),  # canonical host
                    "region_hint": site.get('region_hint'),
                    "public_suffix": site.get('public_suffix'),
                    "base_url": base_url,
                    "tab": tab.get('tab'),
                    "status": tab.get('status'),
                    "message": tab.get('message'),
                    "load_time_s": lt,
                    "load_time_vm_norm_s": vmn,          # <-- new column in Excel
                    "actual_url": tab.get('url'),
                    "expected_url": tab.get('expected_url'),
                    "variant": tab.get('variant') or "root",
                    "vm_performance_factor": Config.VM_PERFORMANCE_FACTOR,
                    "vm_baseline_time": Config.VM_BASELINE_TIME
                })
        df = pd.DataFrame(rows)
        df.to_excel(Config.RESULTS_EXCEL, index=False)
        logger.info(f"📁 Results saved to Excel: {Config.RESULTS_EXCEL}")

    def cleanup_old_audit_logs(self, retention_days=8):
        try:
            if not os.path.exists(Config.AUDIT_LOG):
                return
            cutoff_time = datetime.now(timezone.utc) - timedelta(days=retention_days)
            cutoff_ts = cutoff_time.strftime("%Y-%m-%dT%H:%M:%S.%f")[:-3] + "Z"
            with open(Config.AUDIT_LOG, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            kept, deleted = [], 0
            for line in lines:
                try:
                    entry = json.loads(line.strip())
                    if entry.get('ts', '') >= cutoff_ts:
                        kept.append(line)
                    else:
                        deleted += 1
                except json.JSONDecodeError:
                    kept.append(line)
            if deleted > 0:
                with open(Config.AUDIT_LOG, 'w', encoding='utf-8') as f:
                    f.writelines(kept)
                logger.info(f"🧹 Cleaned {deleted} old audit entries (kept {len(kept)})")
                audit.write({"event": "log_cleanup", "deleted_entries": deleted, "retained_entries": len(kept), "retention_days": retention_days})
        except Exception as e:
            logger.error(f"❌ Failed to cleanup audit logs: {e}")


# ========= MAIN ==========
if __name__ == "__main__":
    print("🚀 Starting VM-Optimized Website Monitor...")
    print("📋 Key Improvements:")
    print("   • Dynamic VM performance calibration")
    print("   • Adjusted load time thresholds (8s/15s/25s)")
    print("   • Enhanced retry logic for VM issues")
    print("   • Improved visual scoring system")
    print("   • VM resource monitoring")
    print("   • Chrome optimizations for VM environments")
    print("="*60)
    
    try:
        WebsiteMonitor().run_monitoring()
        print("✅ Monitoring completed successfully!")
    except KeyboardInterrupt:
        print("\n⚠️ Monitoring interrupted by user")
    except Exception as e:
        print(f"❌ Fatal error: {e}")
        logger.error(f"Fatal error in main: {e}", exc_info=True)
