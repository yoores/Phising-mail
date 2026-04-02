import smtplib
import tkinter as tk
from tkinter import scrolledtext, messagebox, ttk, filedialog, colorchooser
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.base import MIMEBase
from email import encoders
from email.utils import formataddr
import json
import os
import threading
import time
import re
import random
import csv
from datetime import datetime
import requests
import hashlib

# Kiểm tra thư viện socks
try:
    import socks
except ImportError:
    print("Thiếu thư viện pysocks. Vui lòng cài đặt bằng: pip install pysocks")
    exit(1)

# Kiểm tra dnspython (tùy chọn)
try:
    import dns.resolver
    MX_AVAILABLE = True
except ImportError:
    MX_AVAILABLE = False
    print("Cảnh báo: Thiếu dnspython. MX validation sẽ bị vô hiệu hóa. Cài đặt bằng: pip install dnspython")

ACCOUNTS_FILE = "gmail_accounts.json"
SETTINGS_FILE = "settings.json"
PROXIES_FILE = "proxies.txt"
TEMPLATES_FILE = "templates.json"

class EmailSenderApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Phising Mail by @seraphin902")
        self.root.geometry("1300x850")
        self.root.minsize(1100, 750)
        self.root.resizable(True, True)

        # Dữ liệu chính
        self.accounts = []
        self.current_account = None
        self.attachments = []
        self.recipient_list = []
        self.sending_in_progress = False
        self.stop_sending = False

        # Multi-account sending
        self.multi_threads = []
        self.multi_stop = False

        # Auto gửi
        self.auto_running = False
        self.auto_thread = None
        self.auto_stop = False

        # Lock cho file
        self.file_lock = threading.Lock()

        # Cache AI
        self.ai_content_cache = {}

        # Proxy
        self.use_proxy = tk.BooleanVar(value=False)
        self.proxy_type = tk.StringVar(value="SOCKS5")
        self.proxy_address = tk.StringVar()
        self.proxy_username = tk.StringVar()
        self.proxy_password = tk.StringVar()
        self.proxy_list = []
        self.current_proxy_index = 0

        # Cài đặt cơ bản
        self.delay_between = tk.DoubleVar(value=1.0)
        self.max_emails = tk.IntVar(value=0)
        self.stop_on_error = tk.BooleanVar(value=True)
        self.theme_bg = tk.StringVar(value="#f5f5f5")
        self.theme_fg = tk.StringVar(value="#333333")
        self.theme_btn = tk.StringVar(value="#2196F3")

        # Cài đặt tính năng cơ bản
        self.enable_detailed_log = tk.BooleanVar(value=True)
        self.enable_email_validation = tk.BooleanVar(value=True)
        self.enable_auto_save_stats = tk.BooleanVar(value=True)
        self.enable_popup_notification = tk.BooleanVar(value=True)
        self.max_concurrent_sends = tk.IntVar(value=5)
        self.enable_safe_mode = tk.BooleanVar(value=True)
        self.retry_on_error = tk.IntVar(value=0)

        # Anti-spam
        self.anti_random_delay = tk.BooleanVar(value=False)
        self.anti_delay_min = tk.DoubleVar(value=0.5)
        self.anti_delay_max = tk.DoubleVar(value=3.0)
        self.anti_jitter = tk.BooleanVar(value=False)
        self.anti_jitter_percent = tk.DoubleVar(value=20.0)

        self.anti_random_subject = tk.BooleanVar(value=False)
        self.anti_subject_file = tk.StringVar()

        self.anti_random_body = tk.BooleanVar(value=False)
        self.anti_body_file = tk.StringVar()

        self.anti_random_signature = tk.BooleanVar(value=False)
        self.anti_signature_file = tk.StringVar()

        self.anti_random_sender_name = tk.BooleanVar(value=False)
        self.anti_sender_names_file = tk.StringVar()

        self.anti_rotate_proxy = tk.BooleanVar(value=False)
        self.anti_proxy_rotate_on_error = tk.BooleanVar(value=True)
        self.anti_rotate_proxy_per_email = tk.BooleanVar(value=False)

        self.anti_random_attachment = tk.BooleanVar(value=False)
        self.anti_attachment_folder = tk.StringVar()

        self.anti_random_headers = tk.BooleanVar(value=False)
        self.anti_random_html = tk.BooleanVar(value=False)

        self.anti_shuffle_emails = tk.BooleanVar(value=False)
        self.anti_rotate_accounts = tk.BooleanVar(value=False)
        self.anti_random_batch = tk.BooleanVar(value=False)
        self.anti_batch_min = tk.IntVar(value=10)
        self.anti_batch_max = tk.IntVar(value=50)
        self.anti_hidden_content = tk.BooleanVar(value=False)
        self.anti_obfuscate_chars = tk.BooleanVar(value=False)
        self.anti_dummy_image = tk.BooleanVar(value=False)

        # AI Ollama (tinyllama)
        self.ollama_enabled = tk.BooleanVar(value=True)
        self.ollama_url = tk.StringVar(value="http://localhost:11434/api/generate")
        self.ollama_model = tk.StringVar(value="tinyllama:1.1b")
        self.ollama_topic = tk.StringVar(value="giới thiệu sản phẩm/dịch vụ")
        self.ollama_tone = tk.StringVar(value="thân thiện, chuyên nghiệp")
        self.ollama_length = tk.StringVar(value="ngắn gọn (50-80 từ)")
        self.ollama_language = tk.StringVar(value="Tiếng Việt")
        self.ollama_custom_prompt = tk.StringVar(value="")

        # AI cho mỗi email
        self.ai_per_email = tk.BooleanVar(value=True)   # Bật: mỗi email nội dung khác nhau
        self.ai_cache_enabled = tk.BooleanVar(value=False)
        self.ai_max_retries = tk.IntVar(value=3)

        # Nâng cao
        self.custom_smtp = tk.BooleanVar(value=False)
        self.smtp_host = tk.StringVar(value="smtp.gmail.com")
        self.smtp_port = tk.IntVar(value=587)
        self.smtp_use_ssl = tk.BooleanVar(value=False)
        self.enable_mx_validation = tk.BooleanVar(value=False)
        self.merge_fields_file = tk.StringVar()
        self.merge_data = []
        self.merge_headers = []
        self.templates = {}
        self.current_template = tk.StringVar()

        # Auto settings
        self.auto_email_list_file = tk.StringVar()
        self.auto_subject_file = tk.StringVar()
        self.auto_body_file = tk.StringVar()
        self.auto_loop_infinite = tk.BooleanVar(value=True)
        self.auto_loop_count = tk.IntVar(value=1)
        self.auto_batch_delay = tk.DoubleVar(value=60.0)
        self.auto_use_html = tk.BooleanVar(value=False)
        self.auto_selected_accounts = []

        # Tải dữ liệu
        self.load_accounts()
        self.load_settings()
        self.load_proxies_from_file()
        self.load_templates()

        # Tạo giao diện
        self.create_notebook()
        self.create_control_tab()
        self.create_data_tab()
        self.create_advanced_tab()
        self.create_settings_tab()
        self.update_account_list()
        self.apply_theme()

    # ==================== LOAD / SAVE ====================
    def load_accounts(self):
        if os.path.exists(ACCOUNTS_FILE):
            try:
                with open(ACCOUNTS_FILE, 'r', encoding='utf-8') as f:
                    self.accounts = json.load(f)
                for acc in self.accounts:
                    acc.setdefault("sent", 0)
                    acc.setdefault("success", 0)
                    acc.setdefault("error", 0)
                    acc.setdefault("status", "Chưa dùng")
            except:
                self.accounts = []
        else:
            self.accounts = []

    def save_accounts(self):
        with self.file_lock:
            with open(ACCOUNTS_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.accounts, f, ensure_ascii=False, indent=2)

    def load_templates(self):
        if os.path.exists(TEMPLATES_FILE):
            try:
                with open(TEMPLATES_FILE, 'r', encoding='utf-8') as f:
                    self.templates = json.load(f)
            except:
                self.templates = {}
        else:
            self.templates = {}

    def save_templates(self):
        with open(TEMPLATES_FILE, 'w', encoding='utf-8') as f:
            json.dump(self.templates, f, indent=2)

    def load_settings(self):
        if os.path.exists(SETTINGS_FILE):
            try:
                with open(SETTINGS_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    self.delay_between.set(data.get("delay_between", 1.0))
                    self.max_emails.set(data.get("max_emails", 0))
                    self.stop_on_error.set(data.get("stop_on_error", True))
                    self.theme_bg.set(data.get("theme_bg", "#f5f5f5"))
                    self.theme_fg.set(data.get("theme_fg", "#333333"))
                    self.theme_btn.set(data.get("theme_btn", "#2196F3"))

                    self.enable_detailed_log.set(data.get("enable_detailed_log", True))
                    self.enable_email_validation.set(data.get("enable_email_validation", True))
                    self.enable_auto_save_stats.set(data.get("enable_auto_save_stats", True))
                    self.enable_popup_notification.set(data.get("enable_popup_notification", True))
                    self.max_concurrent_sends.set(data.get("max_concurrent_sends", 5))
                    self.enable_safe_mode.set(data.get("enable_safe_mode", True))
                    self.retry_on_error.set(data.get("retry_on_error", 0))

                    self.anti_random_delay.set(data.get("anti_random_delay", False))
                    self.anti_delay_min.set(data.get("anti_delay_min", 0.5))
                    self.anti_delay_max.set(data.get("anti_delay_max", 3.0))
                    self.anti_jitter.set(data.get("anti_jitter", False))
                    self.anti_jitter_percent.set(data.get("anti_jitter_percent", 20.0))

                    self.anti_random_subject.set(data.get("anti_random_subject", False))
                    self.anti_subject_file.set(data.get("anti_subject_file", ""))

                    self.anti_random_body.set(data.get("anti_random_body", False))
                    self.anti_body_file.set(data.get("anti_body_file", ""))

                    self.anti_random_signature.set(data.get("anti_random_signature", False))
                    self.anti_signature_file.set(data.get("anti_signature_file", ""))

                    self.anti_random_sender_name.set(data.get("anti_random_sender_name", False))
                    self.anti_sender_names_file.set(data.get("anti_sender_names_file", ""))

                    self.anti_rotate_proxy.set(data.get("anti_rotate_proxy", False))
                    self.anti_proxy_rotate_on_error.set(data.get("anti_proxy_rotate_on_error", True))
                    self.anti_rotate_proxy_per_email.set(data.get("anti_rotate_proxy_per_email", False))

                    self.anti_random_attachment.set(data.get("anti_random_attachment", False))
                    self.anti_attachment_folder.set(data.get("anti_attachment_folder", ""))

                    self.anti_random_headers.set(data.get("anti_random_headers", False))
                    self.anti_random_html.set(data.get("anti_random_html", False))

                    self.anti_shuffle_emails.set(data.get("anti_shuffle_emails", False))
                    self.anti_rotate_accounts.set(data.get("anti_rotate_accounts", False))
                    self.anti_random_batch.set(data.get("anti_random_batch", False))
                    self.anti_batch_min.set(data.get("anti_batch_min", 10))
                    self.anti_batch_max.set(data.get("anti_batch_max", 50))
                    self.anti_hidden_content.set(data.get("anti_hidden_content", False))
                    self.anti_obfuscate_chars.set(data.get("anti_obfuscate_chars", False))
                    self.anti_dummy_image.set(data.get("anti_dummy_image", False))

                    self.ollama_enabled.set(data.get("ollama_enabled", True))
                    self.ollama_url.set(data.get("ollama_url", "http://localhost:11434/api/generate"))
                    self.ollama_model.set(data.get("ollama_model", "tinyllama:1.1b"))
                    self.ollama_topic.set(data.get("ollama_topic", "giới thiệu sản phẩm/dịch vụ"))
                    self.ollama_tone.set(data.get("ollama_tone", "thân thiện, chuyên nghiệp"))
                    self.ollama_length.set(data.get("ollama_length", "ngắn gọn (50-80 từ)"))
                    self.ollama_language.set(data.get("ollama_language", "Tiếng Việt"))
                    self.ai_per_email.set(data.get("ai_per_email", True))
                    self.ai_cache_enabled.set(data.get("ai_cache_enabled", False))
                    self.ai_max_retries.set(data.get("ai_max_retries", 3))

                    self.custom_smtp.set(data.get("custom_smtp", False))
                    self.smtp_host.set(data.get("smtp_host", "smtp.gmail.com"))
                    self.smtp_port.set(data.get("smtp_port", 587))
                    self.smtp_use_ssl.set(data.get("smtp_use_ssl", False))
                    self.enable_mx_validation.set(data.get("enable_mx_validation", False))

                    self.auto_loop_infinite.set(data.get("auto_loop_infinite", True))
                    self.auto_loop_count.set(data.get("auto_loop_count", 1))
                    self.auto_batch_delay.set(data.get("auto_batch_delay", 60.0))
                    self.auto_use_html.set(data.get("auto_use_html", False))
            except:
                pass

    def save_settings(self):
        data = {
            "delay_between": self.delay_between.get(),
            "max_emails": self.max_emails.get(),
            "stop_on_error": self.stop_on_error.get(),
            "theme_bg": self.theme_bg.get(),
            "theme_fg": self.theme_fg.get(),
            "theme_btn": self.theme_btn.get(),
            "enable_detailed_log": self.enable_detailed_log.get(),
            "enable_email_validation": self.enable_email_validation.get(),
            "enable_auto_save_stats": self.enable_auto_save_stats.get(),
            "enable_popup_notification": self.enable_popup_notification.get(),
            "max_concurrent_sends": self.max_concurrent_sends.get(),
            "enable_safe_mode": self.enable_safe_mode.get(),
            "retry_on_error": self.retry_on_error.get(),
            "anti_random_delay": self.anti_random_delay.get(),
            "anti_delay_min": self.anti_delay_min.get(),
            "anti_delay_max": self.anti_delay_max.get(),
            "anti_jitter": self.anti_jitter.get(),
            "anti_jitter_percent": self.anti_jitter_percent.get(),
            "anti_random_subject": self.anti_random_subject.get(),
            "anti_subject_file": self.anti_subject_file.get(),
            "anti_random_body": self.anti_random_body.get(),
            "anti_body_file": self.anti_body_file.get(),
            "anti_random_signature": self.anti_random_signature.get(),
            "anti_signature_file": self.anti_signature_file.get(),
            "anti_random_sender_name": self.anti_random_sender_name.get(),
            "anti_sender_names_file": self.anti_sender_names_file.get(),
            "anti_rotate_proxy": self.anti_rotate_proxy.get(),
            "anti_proxy_rotate_on_error": self.anti_proxy_rotate_on_error.get(),
            "anti_rotate_proxy_per_email": self.anti_rotate_proxy_per_email.get(),
            "anti_random_attachment": self.anti_random_attachment.get(),
            "anti_attachment_folder": self.anti_attachment_folder.get(),
            "anti_random_headers": self.anti_random_headers.get(),
            "anti_random_html": self.anti_random_html.get(),
            "anti_shuffle_emails": self.anti_shuffle_emails.get(),
            "anti_rotate_accounts": self.anti_rotate_accounts.get(),
            "anti_random_batch": self.anti_random_batch.get(),
            "anti_batch_min": self.anti_batch_min.get(),
            "anti_batch_max": self.anti_batch_max.get(),
            "anti_hidden_content": self.anti_hidden_content.get(),
            "anti_obfuscate_chars": self.anti_obfuscate_chars.get(),
            "anti_dummy_image": self.anti_dummy_image.get(),
            "ollama_enabled": self.ollama_enabled.get(),
            "ollama_url": self.ollama_url.get(),
            "ollama_model": self.ollama_model.get(),
            "ollama_topic": self.ollama_topic.get(),
            "ollama_tone": self.ollama_tone.get(),
            "ollama_length": self.ollama_length.get(),
            "ollama_language": self.ollama_language.get(),
            "ai_per_email": self.ai_per_email.get(),
            "ai_cache_enabled": self.ai_cache_enabled.get(),
            "ai_max_retries": self.ai_max_retries.get(),
            "custom_smtp": self.custom_smtp.get(),
            "smtp_host": self.smtp_host.get(),
            "smtp_port": self.smtp_port.get(),
            "smtp_use_ssl": self.smtp_use_ssl.get(),
            "enable_mx_validation": self.enable_mx_validation.get(),
            "auto_loop_infinite": self.auto_loop_infinite.get(),
            "auto_loop_count": self.auto_loop_count.get(),
            "auto_batch_delay": self.auto_batch_delay.get(),
            "auto_use_html": self.auto_use_html.get()
        }
        with open(SETTINGS_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2)

    def load_proxies_from_file(self):
        if os.path.exists(PROXIES_FILE):
            try:
                with open(PROXIES_FILE, 'r', encoding='utf-8') as f:
                    lines = [line.strip() for line in f if line.strip() and not line.startswith('#')]
                self.proxy_list = []
                for line in lines:
                    parts = line.split(':')
                    if len(parts) == 2:
                        ip, port = parts
                        self.proxy_list.append((ip, int(port), None, None))
                    elif len(parts) == 4:
                        ip, port, user, pwd = parts
                        self.proxy_list.append((ip, int(port), user, pwd))
            except Exception as e:
                print(f"Lỗi đọc proxy file: {e}")
        else:
            with open(PROXIES_FILE, 'w', encoding='utf-8') as f:
                f.write("# Mỗi dòng: ip:port hoặc ip:port:username:password\n")
                f.write("192.168.1.1:8080\n")
                f.write("proxy.example.com:3128:user:pass\n")

    # ==================== GIAO DIỆN ====================
    def create_notebook(self):
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TNotebook', background='#f0f0f0')
        style.configure('TNotebook.Tab', padding=[15, 5], font=('Arial', 10))
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

    def create_control_tab(self):
        """Tab 1: Trung tâm điều khiển"""
        self.control_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.control_tab, text="🎮 Điều khiển")

        paned = ttk.PanedWindow(self.control_tab, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Cột trái: Quản lý tài khoản
        left_frame = ttk.Frame(paned)
        paned.add(left_frame, weight=1)

        acc_frame = tk.LabelFrame(left_frame, text="📋 Quản lý tài khoản", padx=5, pady=5, font=('Arial', 10, 'bold'))
        acc_frame.pack(fill=tk.BOTH, expand=True)

        columns = ("email", "sent", "success", "error", "status")
        self.tree_accounts = ttk.Treeview(acc_frame, columns=columns, show="headings", height=12)
        self.tree_accounts.heading("email", text="Email")
        self.tree_accounts.heading("sent", text="Gửi")
        self.tree_accounts.heading("success", text="OK")
        self.tree_accounts.heading("error", text="Lỗi")
        self.tree_accounts.heading("status", text="Trạng thái")
        self.tree_accounts.column("email", width=200)
        self.tree_accounts.column("sent", width=50)
        self.tree_accounts.column("success", width=50)
        self.tree_accounts.column("error", width=50)
        self.tree_accounts.column("status", width=100)
        self.tree_accounts.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(acc_frame, orient=tk.VERTICAL, command=self.tree_accounts.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree_accounts.configure(yscrollcommand=scrollbar.set)

        btn_acc_frame = tk.Frame(acc_frame)
        btn_acc_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        btn_add = tk.Button(btn_acc_frame, text="➕ Thêm", command=self.add_account, bg="#4CAF50", fg="white", width=8)
        btn_add.pack(pady=2)
        btn_edit = tk.Button(btn_acc_frame, text="✏️ Sửa", command=self.edit_account, bg="#FF9800", fg="white", width=8)
        btn_edit.pack(pady=2)
        btn_delete = tk.Button(btn_acc_frame, text="🗑️ Xóa", command=self.delete_account, bg="#f44336", fg="white", width=8)
        btn_delete.pack(pady=2)
        btn_import = tk.Button(btn_acc_frame, text="📥 Import", command=self.import_accounts_from_file, bg="#2196F3", fg="white", width=8)
        btn_import.pack(pady=2)
        btn_export = tk.Button(btn_acc_frame, text="📤 Export", command=self.export_accounts_to_file, bg="#2196F3", fg="white", width=8)
        btn_export.pack(pady=2)
        btn_reset = tk.Button(btn_acc_frame, text="🔄 Reset", command=self.reset_stats, bg="#9E9E9E", fg="white", width=8)
        btn_reset.pack(pady=2)
        btn_export_stats = tk.Button(btn_acc_frame, text="📊 Xuất thống kê", command=self.export_stats, bg="#FF9800", fg="white", width=10)
        btn_export_stats.pack(pady=2)

        # Cột phải: Điều khiển gửi
        right_frame = ttk.Frame(paned)
        paned.add(right_frame, weight=1)

        # Chọn tài khoản cho gửi đơn
        select_frame = tk.LabelFrame(right_frame, text="📧 Tài khoản gửi đơn", padx=5, pady=5, font=('Arial', 10, 'bold'))
        select_frame.pack(fill=tk.X, pady=(0, 5))
        tk.Label(select_frame, text="Chọn tài khoản:").pack(side=tk.LEFT, padx=5)
        self.account_combo = ttk.Combobox(select_frame, width=35, state="readonly")
        self.account_combo.pack(side=tk.LEFT, padx=5)
        self.account_combo.bind('<<ComboboxSelected>>', self.on_account_selected)
        self.lbl_from = tk.Label(select_frame, text="", fg="green")
        self.lbl_from.pack(side=tk.LEFT, padx=5)

        # Proxy
        proxy_frame = tk.LabelFrame(right_frame, text="🌐 Proxy", padx=5, pady=5, font=('Arial', 10, 'bold'))
        proxy_frame.pack(fill=tk.X, pady=(0, 5))

        chk_proxy = tk.Checkbutton(proxy_frame, text="Sử dụng proxy", variable=self.use_proxy, command=self.toggle_proxy_fields)
        chk_proxy.grid(row=0, column=0, sticky="w", padx=5)

        tk.Label(proxy_frame, text="Loại:").grid(row=0, column=1, padx=5)
        self.proxy_type_combo = ttk.Combobox(proxy_frame, textvariable=self.proxy_type, values=["HTTP", "SOCKS4", "SOCKS5"], state="readonly", width=8)
        self.proxy_type_combo.grid(row=0, column=2, padx=5)

        tk.Label(proxy_frame, text="Địa chỉ:").grid(row=0, column=3, padx=5)
        self.entry_proxy_addr = tk.Entry(proxy_frame, textvariable=self.proxy_address, width=18)
        self.entry_proxy_addr.grid(row=0, column=4, padx=5)

        btn_load_proxy = tk.Button(proxy_frame, text="📂 File", command=self.load_proxy_from_file_dialog, bg="#2196F3", fg="white", width=5)
        btn_load_proxy.grid(row=0, column=5, padx=5)

        tk.Label(proxy_frame, text="User:").grid(row=1, column=1, padx=5, pady=2)
        self.entry_proxy_user = tk.Entry(proxy_frame, textvariable=self.proxy_username, width=12)
        self.entry_proxy_user.grid(row=1, column=2, padx=5, pady=2)

        tk.Label(proxy_frame, text="Pass:").grid(row=1, column=3, padx=5, pady=2)
        self.entry_proxy_pass = tk.Entry(proxy_frame, textvariable=self.proxy_password, show="*", width=12)
        self.entry_proxy_pass.grid(row=1, column=4, padx=5, pady=2)

        self.toggle_proxy_fields()

        # Nút gửi
        send_frame = tk.LabelFrame(right_frame, text="🚀 Gửi email", padx=5, pady=5, font=('Arial', 10, 'bold'))
        send_frame.pack(fill=tk.X, pady=(0, 5))

        btn_frame = tk.Frame(send_frame)
        btn_frame.pack()

        self.btn_single = tk.Button(btn_frame, text="📧 Gửi đơn", command=self.send_single_email, bg="#2196F3", fg="white", width=12)
        self.btn_single.pack(side=tk.LEFT, padx=5, pady=2)

        self.btn_list = tk.Button(btn_frame, text="📤 Gửi danh sách (1 TK)", command=self.send_to_list, bg="#FF9800", fg="white", width=18)
        self.btn_list.pack(side=tk.LEFT, padx=5, pady=2)

        self.btn_all = tk.Button(btn_frame, text="🌐 Gửi danh sách (tất cả TK)", command=self.send_to_all_accounts, bg="#9C27B0", fg="white", width=22)
        self.btn_all.pack(side=tk.LEFT, padx=5, pady=2)

        self.btn_stop = tk.Button(btn_frame, text="⏹ Dừng", command=self.stop_sending, bg="#f44336", fg="white", state=tk.DISABLED, width=8)
        self.btn_stop.pack(side=tk.LEFT, padx=5, pady=2)

        # Auto
        auto_frame = tk.LabelFrame(right_frame, text="🤖 Auto gửi (chọn nhiều tài khoản)", padx=5, pady=5, font=('Arial', 10, 'bold'))
        auto_frame.pack(fill=tk.X, pady=(0, 5))

        self.auto_accounts_frame = tk.Frame(auto_frame)
        self.auto_accounts_frame.pack(fill=tk.X, pady=5)
        tk.Label(self.auto_accounts_frame, text="Chọn tài khoản để auto (giữ Ctrl để chọn nhiều):").pack(anchor="w")
        self.auto_accounts_listbox = tk.Listbox(self.auto_accounts_frame, selectmode=tk.MULTIPLE, height=4)
        self.auto_accounts_listbox.pack(fill=tk.X, padx=5, pady=2)

        btn_auto_frame = tk.Frame(auto_frame)
        btn_auto_frame.pack()
        self.btn_auto_start = tk.Button(btn_auto_frame, text="▶ Bắt đầu Auto", command=self.start_auto, bg="#4CAF50", fg="white", width=12)
        self.btn_auto_start.pack(side=tk.LEFT, padx=5)
        self.btn_auto_stop = tk.Button(btn_auto_frame, text="⏹ Dừng Auto", command=self.stop_auto, bg="#f44336", fg="white", width=12)
        self.btn_auto_stop.pack(side=tk.LEFT, padx=5)
        self.auto_status_label = tk.Label(auto_frame, text="", fg="blue")
        self.auto_status_label.pack(pady=2)

        # Log và tiến độ
        log_frame = tk.LabelFrame(right_frame, text="📝 Log & Tiến độ", padx=5, pady=5, font=('Arial', 10, 'bold'))
        log_frame.pack(fill=tk.BOTH, expand=True)

        self.status_label = tk.Label(log_frame, text="", fg="black")
        self.status_label.pack(pady=2)

        self.progress_bar = ttk.Progressbar(log_frame, orient=tk.HORIZONTAL, length=400, mode='determinate')
        self.progress_bar.pack(pady=2)

        self.multi_progress_label = tk.Label(log_frame, text="", fg="blue")
        self.multi_progress_label.pack()
        self.multi_progress_bar = ttk.Progressbar(log_frame, orient=tk.HORIZONTAL, length=400, mode='determinate')
        self.multi_progress_bar.pack(pady=2)

        self.auto_log = scrolledtext.ScrolledText(log_frame, width=50, height=8, state=tk.DISABLED)
        self.auto_log.pack(fill=tk.BOTH, expand=True, pady=2)

    def create_data_tab(self):
        """Tab 2: Dữ liệu gửi và AI"""
        self.data_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.data_tab, text="📝 Dữ liệu & AI")

        # Canvas cho scroll
        canvas = tk.Canvas(self.data_tab)
        scrollbar = ttk.Scrollbar(self.data_tab, orient="vertical", command=canvas.yview)
        scrollable_frame = tk.Frame(canvas)

        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )

        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        # Người nhận
        recipient_frame = tk.LabelFrame(scrollable_frame, text="📬 Người nhận", padx=5, pady=5, font=('Arial', 10, 'bold'))
        recipient_frame.pack(fill=tk.X, pady=(0, 10), padx=5)

        row1 = tk.Frame(recipient_frame)
        row1.pack(fill=tk.X, pady=2)
        tk.Label(row1, text="Email đơn:").pack(side=tk.LEFT, padx=5)
        self.entry_to = tk.Entry(row1, width=50)
        self.entry_to.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)

        row2 = tk.Frame(recipient_frame)
        row2.pack(fill=tk.X, pady=2)
        tk.Label(row2, text="Danh sách file:").pack(side=tk.LEFT, padx=5)
        btn_load = tk.Button(row2, text="📂 Chọn file .txt", command=self.load_recipient_file, bg="#2196F3", fg="white")
        btn_load.pack(side=tk.LEFT, padx=5)
        self.lbl_recipient_count = tk.Label(row2, text="", fg="green")
        self.lbl_recipient_count.pack(side=tk.LEFT, padx=5)

        btn_clear_list = tk.Button(row2, text="🗑️ Xóa danh sách", command=self.clear_recipient_list, bg="#f44336", fg="white")
        btn_clear_list.pack(side=tk.LEFT, padx=5)

        btn_deduplicate = tk.Button(row2, text="🔍 Lọc trùng", command=self.deduplicate_emails, bg="#FF9800", fg="white")
        btn_deduplicate.pack(side=tk.LEFT, padx=5)

        btn_validate = tk.Button(row2, text="✅ Kiểm tra email", command=self.validate_emails, bg="#4CAF50", fg="white")
        btn_validate.pack(side=tk.LEFT, padx=5)

        self.recipient_listbox = tk.Listbox(recipient_frame, height=5, selectmode=tk.SINGLE)
        self.recipient_listbox.pack(fill=tk.X, padx=5, pady=5)

        # Nội dung
        content_frame = tk.LabelFrame(scrollable_frame, text="📄 Nội dung email mẫu", padx=5, pady=5, font=('Arial', 10, 'bold'))
        content_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 10), padx=5)

        tk.Label(content_frame, text="Chủ đề mẫu:").grid(row=0, column=0, sticky="w", pady=2, padx=5)
        self.entry_subject = tk.Entry(content_frame, width=60)
        self.entry_subject.grid(row=0, column=1, pady=2, padx=5, sticky="ew")

        tk.Label(content_frame, text="Nội dung mẫu:").grid(row=1, column=0, sticky="nw", pady=2, padx=5)
        self.text_body = scrolledtext.ScrolledText(content_frame, width=60, height=8)
        self.text_body.grid(row=1, column=1, pady=2, padx=5, sticky="ew")

        btn_content_frame = tk.Frame(content_frame)
        btn_content_frame.grid(row=2, column=1, sticky="w", pady=5)

        btn_save_content = tk.Button(btn_content_frame, text="💾 Lưu nội dung", command=self.save_content_to_file, bg="#4CAF50", fg="white")
        btn_save_content.pack(side=tk.LEFT, padx=2)

        btn_load_content = tk.Button(btn_content_frame, text="📂 Tải nội dung", command=self.load_content_from_file, bg="#2196F3", fg="white")
        btn_load_content.pack(side=tk.LEFT, padx=2)

        btn_preview_html = tk.Button(btn_content_frame, text="👁️ Xem trước HTML", command=self.preview_html, bg="#9C27B0", fg="white")
        btn_preview_html.pack(side=tk.LEFT, padx=2)

        self.var_html = tk.BooleanVar()
        chk_html = tk.Checkbutton(content_frame, text="Gửi dạng HTML", variable=self.var_html)
        chk_html.grid(row=3, column=1, sticky="w", pady=2, padx=5)

        content_frame.columnconfigure(1, weight=1)

        # File đính kèm
        attach_frame = tk.LabelFrame(scrollable_frame, text="📎 File đính kèm", padx=5, pady=5, font=('Arial', 10, 'bold'))
        attach_frame.pack(fill=tk.X, pady=(0, 10), padx=5)

        self.attach_listbox = tk.Listbox(attach_frame, height=3)
        self.attach_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)

        btn_attach_frame = tk.Frame(attach_frame)
        btn_attach_frame.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        btn_add = tk.Button(btn_attach_frame, text="➕ Thêm", command=self.add_attachment, bg="#4CAF50", fg="white", width=8)
        btn_add.pack(pady=2)
        btn_remove = tk.Button(btn_attach_frame, text="🗑️ Xóa", command=self.remove_attachment, bg="#f44336", fg="white", width=8)
        btn_remove.pack(pady=2)
        btn_remove_all = tk.Button(btn_attach_frame, text="🗑️ Xóa tất cả", command=self.remove_all_attachments, bg="#f44336", fg="white", width=8)
        btn_remove_all.pack(pady=2)

        # AI Ollama (tạo nội dung khác nhau cho mỗi email)
        ai_frame = tk.LabelFrame(scrollable_frame, text="🤖 AI Ollama (tinyllama:1.1b) - Tạo nội dung khác nhau cho mỗi email", padx=5, pady=5, font=('Arial', 10, 'bold'))
        ai_frame.pack(fill=tk.X, padx=5, pady=5)

        # Dòng 0: Chủ đề
        tk.Label(ai_frame, text="📌 Chủ đề:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        entry_topic = tk.Entry(ai_frame, textvariable=self.ollama_topic, width=50)
        entry_topic.grid(row=0, column=1, padx=5, pady=2, sticky="ew")
        tk.Label(ai_frame, text="VD: giới thiệu khóa học, bán hàng, tuyển dụng...").grid(row=0, column=2, padx=5, pady=2)

        # Dòng 1: Phong cách
        tk.Label(ai_frame, text="🎨 Phong cách:").grid(row=1, column=0, sticky="w", padx=5, pady=2)
        self.tone_combo = ttk.Combobox(ai_frame, textvariable=self.ollama_tone,
                                       values=["chuyên nghiệp, lịch sự", "thân thiện, gần gũi", "hài hước, vui vẻ",
                                               "ngắn gọn, súc tích", "chi tiết, đầy đủ thông tin"], width=50)
        self.tone_combo.grid(row=1, column=1, padx=5, pady=2, sticky="ew")

        # Dòng 2: Độ dài
        tk.Label(ai_frame, text="📏 Độ dài:").grid(row=2, column=0, sticky="w", padx=5, pady=2)
        self.length_combo = ttk.Combobox(ai_frame, textvariable=self.ollama_length,
                                         values=["cực ngắn (2-3 câu)", "ngắn (50-80 từ)", "vừa (100-150 từ)", "dài (200-300 từ)"], width=50)
        self.length_combo.grid(row=2, column=1, padx=5, pady=2, sticky="ew")

        # Dòng 3: Ngôn ngữ
        tk.Label(ai_frame, text="🌐 Ngôn ngữ:").grid(row=3, column=0, sticky="w", padx=5, pady=2)
        self.lang_combo = ttk.Combobox(ai_frame, textvariable=self.ollama_language,
                                       values=["Tiếng Việt", "Tiếng Anh", "Tiếng Việt pha tiếng Anh"], width=50)
        self.lang_combo.grid(row=3, column=1, padx=5, pady=2, sticky="ew")

        # Dòng 4: Tùy chọn AI
        options_frame = tk.Frame(ai_frame)
        options_frame.grid(row=4, column=0, columnspan=3, pady=5)
        chk_per_email = tk.Checkbutton(options_frame, text="✅ Bật: Mỗi email có nội dung khác nhau (AI sinh riêng)",
                                       variable=self.ai_per_email, font=('Arial', 9, 'bold'))
        chk_per_email.pack(side=tk.LEFT, padx=10)
        chk_cache = tk.Checkbutton(options_frame, text="Bật cache (tránh trùng nội dung)", variable=self.ai_cache_enabled)
        chk_cache.pack(side=tk.LEFT, padx=10)
        tk.Label(options_frame, text="Số lần thử:").pack(side=tk.LEFT, padx=5)
        spin_retry = tk.Spinbox(options_frame, from_=1, to=5, textvariable=self.ai_max_retries, width=5)
        spin_retry.pack(side=tk.LEFT)

        # Dòng 5: Prompt tùy chỉnh
        tk.Label(ai_frame, text="✏️ Prompt tùy chỉnh (để trống dùng mặc định):").grid(row=5, column=0, sticky="w", padx=5, pady=2)
        entry_custom = tk.Entry(ai_frame, textvariable=self.ollama_custom_prompt, width=80)
        entry_custom.grid(row=5, column=1, columnspan=2, padx=5, pady=2, sticky="ew")

        # Dòng 6: Nút test và xóa cache
        btn_test_ai = tk.Button(ai_frame, text="🧪 Kiểm tra AI (tạo 1 mẫu)", command=self.generate_with_ollama,
                                bg="#8E44AD", fg="white", width=20)
        btn_test_ai.grid(row=6, column=0, pady=5, padx=5)
        btn_clear_cache = tk.Button(ai_frame, text="🔄 Xóa cache AI", command=self.clear_ai_cache,
                                    bg="#FF9800", fg="white", width=20)
        btn_clear_cache.grid(row=6, column=1, pady=5, padx=5)

        ai_frame.columnconfigure(1, weight=1)

    def create_advanced_tab(self):
        """Tab 3: Tính năng nâng cao"""
        self.advanced_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.advanced_tab, text="⚡ Nâng cao")

        paned = ttk.PanedWindow(self.advanced_tab, orient=tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        left_frame = ttk.Frame(paned)
        paned.add(left_frame, weight=1)

        # Custom SMTP
        smtp_frame = tk.LabelFrame(left_frame, text="🔧 SMTP tùy chỉnh", padx=5, pady=5)
        smtp_frame.pack(fill=tk.X, pady=(0, 5))

        chk_custom_smtp = tk.Checkbutton(smtp_frame, text="Sử dụng SMTP tùy chỉnh", variable=self.custom_smtp, command=self.toggle_custom_smtp)
        chk_custom_smtp.grid(row=0, column=0, columnspan=3, sticky="w", pady=2, padx=5)

        tk.Label(smtp_frame, text="Host:").grid(row=1, column=0, sticky="w", pady=2, padx=5)
        self.entry_smtp_host = tk.Entry(smtp_frame, textvariable=self.smtp_host, width=25)
        self.entry_smtp_host.grid(row=1, column=1, pady=2, padx=5)

        tk.Label(smtp_frame, text="Port:").grid(row=2, column=0, sticky="w", pady=2, padx=5)
        self.entry_smtp_port = tk.Entry(smtp_frame, textvariable=self.smtp_port, width=10)
        self.entry_smtp_port.grid(row=2, column=1, sticky="w", pady=2, padx=5)

        chk_ssl = tk.Checkbutton(smtp_frame, text="Sử dụng SSL", variable=self.smtp_use_ssl)
        chk_ssl.grid(row=2, column=2, sticky="w", pady=2, padx=5)

        btn_test_smtp = tk.Button(smtp_frame, text="🔌 Kiểm tra kết nối", command=self.test_smtp_connection, bg="#4CAF50", fg="white")
        btn_test_smtp.grid(row=3, column=0, columnspan=3, pady=5)

        self.smtp_test_label = tk.Label(smtp_frame, text="", fg="black")
        self.smtp_test_label.grid(row=4, column=0, columnspan=3, pady=2)

        self.toggle_custom_smtp()

        # Templates
        template_frame = tk.LabelFrame(left_frame, text="📁 Mẫu email", padx=5, pady=5)
        template_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

        tk.Label(template_frame, text="Chọn mẫu:").grid(row=0, column=0, sticky="w", pady=2, padx=5)
        self.template_combo = ttk.Combobox(template_frame, textvariable=self.current_template, width=30, state="readonly")
        self.template_combo.grid(row=0, column=1, pady=2, padx=5)
        self.template_combo.bind('<<ComboboxSelected>>', self.load_template)

        btn_save_template = tk.Button(template_frame, text="💾 Lưu mẫu", command=self.save_template, bg="#4CAF50", fg="white")
        btn_save_template.grid(row=0, column=2, padx=5)

        btn_delete_template = tk.Button(template_frame, text="🗑️ Xóa mẫu", command=self.delete_template, bg="#f44336", fg="white")
        btn_delete_template.grid(row=0, column=3, padx=5)

        # Cột phải
        right_frame = ttk.Frame(paned)
        paned.add(right_frame, weight=1)

        # Merge fields
        merge_frame = tk.LabelFrame(right_frame, text="📊 Cá nhân hóa (Merge fields)", padx=5, pady=5)
        merge_frame.pack(fill=tk.X, pady=(0, 5))

        tk.Label(merge_frame, text="File CSV (có header):").grid(row=0, column=0, sticky="w", pady=2, padx=5)
        self.entry_merge_file = tk.Entry(merge_frame, textvariable=self.merge_fields_file, width=35)
        self.entry_merge_file.grid(row=0, column=1, pady=2, padx=5)
        btn_browse_csv = tk.Button(merge_frame, text="Chọn file", command=self.load_merge_file, bg="#2196F3", fg="white")
        btn_browse_csv.grid(row=0, column=2, padx=5)

        self.merge_preview = tk.Text(merge_frame, height=5, width=50, state=tk.DISABLED)
        self.merge_preview.grid(row=1, column=0, columnspan=3, pady=5, padx=5)

        tk.Label(merge_frame, text="Cách dùng: {tên_cột} trong nội dung email").grid(row=2, column=0, columnspan=3, sticky="w", pady=2, padx=5)

        # MX Validation
        mx_frame = tk.LabelFrame(right_frame, text="🔍 Xác thực MX", padx=5, pady=5)
        mx_frame.pack(fill=tk.X, pady=(0, 5))

        chk_mx = tk.Checkbutton(mx_frame, text="Kiểm tra MX record trước khi gửi", variable=self.enable_mx_validation)
        chk_mx.pack(anchor="w", pady=2, padx=5)

        if not MX_AVAILABLE:
            tk.Label(mx_frame, text="⚠️ Cần cài dnspython để dùng tính năng này: pip install dnspython", fg="red").pack(anchor="w", padx=5)

    def create_settings_tab(self):
        """Tab 4: Cài đặt"""
        self.settings_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.settings_tab, text="⚙️ Cài đặt")

        canvas = tk.Canvas(self.settings_tab, bg=self.theme_bg.get())
        scrollbar = ttk.Scrollbar(self.settings_tab, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)

        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )

        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        # Cài đặt gửi
        send_frame = tk.LabelFrame(scrollable_frame, text="⚙️ Cài đặt gửi", padx=5, pady=5)
        send_frame.pack(fill=tk.X, padx=5, pady=5)

        tk.Label(send_frame, text="Delay giữa email (giây):").grid(row=0, column=0, sticky="w", pady=2, padx=5)
        spin_delay = tk.Spinbox(send_frame, from_=0.1, to=60, increment=0.5, textvariable=self.delay_between, width=10)
        spin_delay.grid(row=0, column=1, pady=2, padx=5)

        tk.Label(send_frame, text="Giới hạn số lượng (0=all):").grid(row=1, column=0, sticky="w", pady=2, padx=5)
        spin_max = tk.Spinbox(send_frame, from_=0, to=10000, increment=1, textvariable=self.max_emails, width=10)
        spin_max.grid(row=1, column=1, pady=2, padx=5)

        chk_stop = tk.Checkbutton(send_frame, text="Dừng khi gặp lỗi", variable=self.stop_on_error)
        chk_stop.grid(row=2, column=0, columnspan=2, sticky="w", pady=2, padx=5)

        # Tính năng cơ bản
        features_frame = tk.LabelFrame(scrollable_frame, text="🔧 Tính năng", padx=5, pady=5)
        features_frame.pack(fill=tk.X, padx=5, pady=5)

        chk_detailed_log = tk.Checkbutton(features_frame, text="Hiển thị log chi tiết", variable=self.enable_detailed_log)
        chk_detailed_log.grid(row=0, column=0, sticky="w", pady=2, padx=5)

        chk_email_validation = tk.Checkbutton(features_frame, text="Xác thực email trước khi gửi", variable=self.enable_email_validation)
        chk_email_validation.grid(row=1, column=0, sticky="w", pady=2, padx=5)

        chk_auto_save = tk.Checkbutton(features_frame, text="Tự động lưu thống kê", variable=self.enable_auto_save_stats)
        chk_auto_save.grid(row=2, column=0, sticky="w", pady=2, padx=5)

        chk_popup = tk.Checkbutton(features_frame, text="Hiển thị thông báo popup", variable=self.enable_popup_notification)
        chk_popup.grid(row=3, column=0, sticky="w", pady=2, padx=5)

        chk_safe_mode = tk.Checkbutton(features_frame, text="Chế độ an toàn (xác nhận trước khi gửi hàng loạt)", variable=self.enable_safe_mode)
        chk_safe_mode.grid(row=4, column=0, sticky="w", pady=2, padx=5)

        tk.Label(features_frame, text="Gửi song song tối đa:").grid(row=5, column=0, sticky="w", pady=2, padx=5)
        spin_concurrent = tk.Spinbox(features_frame, from_=1, to=20, increment=1, textvariable=self.max_concurrent_sends, width=10)
        spin_concurrent.grid(row=5, column=1, sticky="w", pady=2, padx=5)

        tk.Label(features_frame, text="Số lần thử lại khi lỗi:").grid(row=6, column=0, sticky="w", pady=2, padx=5)
        spin_retry = tk.Spinbox(features_frame, from_=0, to=5, increment=1, textvariable=self.retry_on_error, width=10)
        spin_retry.grid(row=6, column=1, sticky="w", pady=2, padx=5)

        # Anti-spam
        anti_frame = tk.LabelFrame(scrollable_frame, text="🛡️ Anti-spam / Anti-block", padx=5, pady=5)
        anti_frame.pack(fill=tk.X, padx=5, pady=5)

        row = 0
        chk_rand_delay = tk.Checkbutton(anti_frame, text="Delay ngẫu nhiên", variable=self.anti_random_delay)
        chk_rand_delay.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        tk.Label(anti_frame, text="Min (s):").grid(row=row, column=1, padx=2)
        spin_min = tk.Spinbox(anti_frame, from_=0.1, to=30, increment=0.1, textvariable=self.anti_delay_min, width=6)
        spin_min.grid(row=row, column=2, padx=2)
        tk.Label(anti_frame, text="Max (s):").grid(row=row, column=3, padx=2)
        spin_max = tk.Spinbox(anti_frame, from_=0.1, to=30, increment=0.1, textvariable=self.anti_delay_max, width=6)
        spin_max.grid(row=row, column=4, padx=2)
        chk_jitter = tk.Checkbutton(anti_frame, text="Jitter ±%", variable=self.anti_jitter)
        chk_jitter.grid(row=row, column=5, padx=5)
        spin_jitter = tk.Spinbox(anti_frame, from_=1, to=100, increment=1, textvariable=self.anti_jitter_percent, width=5)
        spin_jitter.grid(row=row, column=6, padx=2)

        row += 1
        chk_rand_subject = tk.Checkbutton(anti_frame, text="Chủ đề ngẫu nhiên", variable=self.anti_random_subject)
        chk_rand_subject.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        entry_subject_file = tk.Entry(anti_frame, textvariable=self.anti_subject_file, width=30)
        entry_subject_file.grid(row=row, column=1, columnspan=3, padx=5)
        btn_subject_file = tk.Button(anti_frame, text="Chọn file", command=self.browse_anti_subject_file)
        btn_subject_file.grid(row=row, column=4, padx=2)

        row += 1
        chk_rand_body = tk.Checkbutton(anti_frame, text="Nội dung ngẫu nhiên", variable=self.anti_random_body)
        chk_rand_body.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        entry_body_file = tk.Entry(anti_frame, textvariable=self.anti_body_file, width=30)
        entry_body_file.grid(row=row, column=1, columnspan=3, padx=5)
        btn_body_file = tk.Button(anti_frame, text="Chọn file", command=self.browse_anti_body_file)
        btn_body_file.grid(row=row, column=4, padx=2)

        row += 1
        chk_rand_sig = tk.Checkbutton(anti_frame, text="Chữ ký ngẫu nhiên", variable=self.anti_random_signature)
        chk_rand_sig.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        entry_sig_file = tk.Entry(anti_frame, textvariable=self.anti_signature_file, width=30)
        entry_sig_file.grid(row=row, column=1, columnspan=3, padx=5)
        btn_sig_file = tk.Button(anti_frame, text="Chọn file", command=self.browse_anti_signature_file)
        btn_sig_file.grid(row=row, column=4, padx=2)

        row += 1
        chk_rand_name = tk.Checkbutton(anti_frame, text="Tên hiển thị ngẫu nhiên", variable=self.anti_random_sender_name)
        chk_rand_name.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        entry_name_file = tk.Entry(anti_frame, textvariable=self.anti_sender_names_file, width=30)
        entry_name_file.grid(row=row, column=1, columnspan=3, padx=5)
        btn_name_file = tk.Button(anti_frame, text="Chọn file", command=self.browse_anti_sender_names_file)
        btn_name_file.grid(row=row, column=4, padx=2)

        row += 1
        chk_rotate_proxy = tk.Checkbutton(anti_frame, text="Luân phiên proxy", variable=self.anti_rotate_proxy)
        chk_rotate_proxy.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        chk_proxy_on_error = tk.Checkbutton(anti_frame, text="Đổi proxy khi lỗi", variable=self.anti_proxy_rotate_on_error)
        chk_proxy_on_error.grid(row=row, column=1, columnspan=2, sticky="w", pady=2)
        chk_proxy_per_email = tk.Checkbutton(anti_frame, text="Đổi proxy mỗi email", variable=self.anti_rotate_proxy_per_email)
        chk_proxy_per_email.grid(row=row, column=3, columnspan=2, sticky="w", pady=2)

        row += 1
        chk_rand_attach = tk.Checkbutton(anti_frame, text="File đính kèm ngẫu nhiên", variable=self.anti_random_attachment)
        chk_rand_attach.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        entry_attach_folder = tk.Entry(anti_frame, textvariable=self.anti_attachment_folder, width=30)
        entry_attach_folder.grid(row=row, column=1, columnspan=3, padx=5)
        btn_attach_folder = tk.Button(anti_frame, text="Chọn thư mục", command=self.browse_anti_attachment_folder)
        btn_attach_folder.grid(row=row, column=4, padx=2)

        row += 1
        chk_rand_headers = tk.Checkbutton(anti_frame, text="Header X-Mailer ngẫu nhiên", variable=self.anti_random_headers)
        chk_rand_headers.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        chk_rand_html = tk.Checkbutton(anti_frame, text="Ngẫu nhiên HTML/Plain", variable=self.anti_random_html)
        chk_rand_html.grid(row=row, column=1, columnspan=2, sticky="w", pady=2)

        row += 1
        chk_shuffle = tk.Checkbutton(anti_frame, text="Xáo trộn danh sách email", variable=self.anti_shuffle_emails)
        chk_shuffle.grid(row=row, column=0, sticky="w", pady=2, padx=5)

        row += 1
        chk_rotate_acc = tk.Checkbutton(anti_frame, text="Xoay tài khoản gửi", variable=self.anti_rotate_accounts)
        chk_rotate_acc.grid(row=row, column=0, sticky="w", pady=2, padx=5)

        row += 1
        chk_random_batch = tk.Checkbutton(anti_frame, text="Batch ngẫu nhiên", variable=self.anti_random_batch)
        chk_random_batch.grid(row=row, column=0, sticky="w", pady=2, padx=5)
        tk.Label(anti_frame, text="Min size:").grid(row=row, column=1, padx=2)
        spin_batch_min = tk.Spinbox(anti_frame, from_=1, to=500, textvariable=self.anti_batch_min, width=5)
        spin_batch_min.grid(row=row, column=2, padx=2)
        tk.Label(anti_frame, text="Max size:").grid(row=row, column=3, padx=2)
        spin_batch_max = tk.Spinbox(anti_frame, from_=1, to=500, textvariable=self.anti_batch_max, width=5)
        spin_batch_max.grid(row=row, column=4, padx=2)

        row += 1
        chk_hidden = tk.Checkbutton(anti_frame, text="Nội dung ẩn (HTML)", variable=self.anti_hidden_content)
        chk_hidden.grid(row=row, column=0, sticky="w", pady=2, padx=5)

        row += 1
        chk_obfuscate = tk.Checkbutton(anti_frame, text="Biến đổi ký tự (Plain text)", variable=self.anti_obfuscate_chars)
        chk_obfuscate.grid(row=row, column=0, sticky="w", pady=2, padx=5)

        row += 1
        chk_dummy_img = tk.Checkbutton(anti_frame, text="Đính kèm ảnh dummy", variable=self.anti_dummy_image)
        chk_dummy_img.grid(row=row, column=0, sticky="w", pady=2, padx=5)

        # Cài đặt AI
        ai_settings_frame = tk.LabelFrame(scrollable_frame, text="🤖 Cài đặt AI Ollama", padx=5, pady=5)
        ai_settings_frame.pack(fill=tk.X, padx=5, pady=5)

        chk_ollama = tk.Checkbutton(ai_settings_frame, text="Bật AI Ollama", variable=self.ollama_enabled)
        chk_ollama.grid(row=0, column=0, sticky="w", pady=2, padx=5)

        tk.Label(ai_settings_frame, text="API URL:").grid(row=1, column=0, sticky="w", pady=2, padx=5)
        entry_url = tk.Entry(ai_settings_frame, textvariable=self.ollama_url, width=50)
        entry_url.grid(row=1, column=1, pady=2, padx=5)

        tk.Label(ai_settings_frame, text="Model:").grid(row=2, column=0, sticky="w", pady=2, padx=5)
        entry_model = tk.Entry(ai_settings_frame, textvariable=self.ollama_model, width=20)
        entry_model.grid(row=2, column=1, sticky="w", pady=2, padx=5)

        # Auto settings
        auto_frame = tk.LabelFrame(scrollable_frame, text="🤖 Cài đặt Auto", padx=5, pady=5)
        auto_frame.pack(fill=tk.X, padx=5, pady=5)

        tk.Label(auto_frame, text="File danh sách email:").grid(row=0, column=0, sticky="w", pady=2, padx=5)
        entry_email = tk.Entry(auto_frame, textvariable=self.auto_email_list_file, width=40)
        entry_email.grid(row=0, column=1, pady=2, padx=5)
        btn_email = tk.Button(auto_frame, text="Chọn", command=self.browse_auto_email_list, width=5)
        btn_email.grid(row=0, column=2, padx=5)

        tk.Label(auto_frame, text="File chủ đề:").grid(row=1, column=0, sticky="w", pady=2, padx=5)
        entry_sub = tk.Entry(auto_frame, textvariable=self.auto_subject_file, width=40)
        entry_sub.grid(row=1, column=1, pady=2, padx=5)
        btn_sub = tk.Button(auto_frame, text="Chọn", command=self.browse_auto_subject, width=5)
        btn_sub.grid(row=1, column=2, padx=5)

        tk.Label(auto_frame, text="File nội dung:").grid(row=2, column=0, sticky="w", pady=2, padx=5)
        entry_body = tk.Entry(auto_frame, textvariable=self.auto_body_file, width=40)
        entry_body.grid(row=2, column=1, pady=2, padx=5)
        btn_body = tk.Button(auto_frame, text="Chọn", command=self.browse_auto_body, width=5)
        btn_body.grid(row=2, column=2, padx=5)

        chk_html = tk.Checkbutton(auto_frame, text="Gửi dạng HTML", variable=self.auto_use_html)
        chk_html.grid(row=3, column=0, sticky="w", pady=2, padx=5)

        frame_loop = tk.Frame(auto_frame)
        frame_loop.grid(row=4, column=0, columnspan=3, sticky="w", pady=2, padx=5)
        chk_infinite = tk.Checkbutton(frame_loop, text="Lặp vô hạn", variable=self.auto_loop_infinite)
        chk_infinite.pack(side=tk.LEFT)
        tk.Label(frame_loop, text="Số lần lặp:").pack(side=tk.LEFT, padx=5)
        spin_loop = tk.Spinbox(frame_loop, from_=1, to=9999, textvariable=self.auto_loop_count, width=6)
        spin_loop.pack(side=tk.LEFT)

        tk.Label(auto_frame, text="Delay giữa các lần (giây):").grid(row=5, column=0, sticky="w", pady=2, padx=5)
        spin_batch = tk.Spinbox(auto_frame, from_=1, to=3600, textvariable=self.auto_batch_delay, width=10)
        spin_batch.grid(row=5, column=1, sticky="w", pady=2, padx=5)

        # Giao diện
        theme_frame = tk.LabelFrame(scrollable_frame, text="🎨 Giao diện", padx=5, pady=5)
        theme_frame.pack(fill=tk.X, padx=5, pady=5)

        tk.Label(theme_frame, text="Màu nền:").grid(row=0, column=0, sticky="w", pady=2, padx=5)
        btn_bg = tk.Button(theme_frame, text="Chọn", command=self.choose_bg_color, bg=self.theme_bg.get(), width=8)
        btn_bg.grid(row=0, column=1, padx=5)

        tk.Label(theme_frame, text="Màu chữ:").grid(row=1, column=0, sticky="w", pady=2, padx=5)
        btn_fg = tk.Button(theme_frame, text="Chọn", command=self.choose_fg_color, bg=self.theme_fg.get(), width=8)
        btn_fg.grid(row=1, column=1, padx=5)

        tk.Label(theme_frame, text="Màu nút:").grid(row=2, column=0, sticky="w", pady=2, padx=5)
        btn_btn = tk.Button(theme_frame, text="Chọn", command=self.choose_btn_color, bg=self.theme_btn.get(), width=8)
        btn_btn.grid(row=2, column=1, padx=5)

        btn_apply = tk.Button(theme_frame, text="Áp dụng", command=self.apply_theme, bg="#4CAF50", fg="white", width=10)
        btn_apply.grid(row=3, column=0, columnspan=2, pady=10)

        btn_save = tk.Button(scrollable_frame, text="💾 Lưu cài đặt", command=self.save_settings, bg="#2196F3", fg="white", width=15)
        btn_save.pack(pady=10)

    # ==================== CÁC HÀM XỬ LÝ ====================
    def toggle_custom_smtp(self):
        if self.custom_smtp.get():
            self.entry_smtp_host.config(state=tk.NORMAL)
            self.entry_smtp_port.config(state=tk.NORMAL)
        else:
            self.entry_smtp_host.config(state=tk.DISABLED)
            self.entry_smtp_port.config(state=tk.DISABLED)

    def test_smtp_connection(self):
        if not self.current_account:
            messagebox.showwarning("Chưa chọn tài khoản", "Vui lòng chọn tài khoản để kiểm tra")
            return
        host = self.smtp_host.get()
        port = self.smtp_port.get()
        use_ssl = self.smtp_use_ssl.get()
        email = self.current_account['email']
        password = self.current_account['password']

        self.smtp_test_label.config(text="Đang kiểm tra...", fg="blue")
        self.root.update()

        def test():
            try:
                if use_ssl:
                    server = smtplib.SMTP_SSL(host, port)
                else:
                    server = smtplib.SMTP(host, port)
                    server.starttls()
                server.login(email, password)
                server.quit()
                self.root.after(0, lambda: self.smtp_test_label.config(text="✅ Kết nối thành công!", fg="green"))
                if self.enable_popup_notification.get():
                    messagebox.showinfo("Thành công", "Kết nối SMTP thành công!")
            except Exception as e:
                self.root.after(0, lambda: self.smtp_test_label.config(text=f"❌ Lỗi: {e}", fg="red"))
                if self.enable_popup_notification.get():
                    messagebox.showerror("Lỗi", f"Kết nối thất bại:\n{e}")
        threading.Thread(target=test, daemon=True).start()

    def save_template(self):
        name = tk.simpledialog.askstring("Lưu mẫu", "Nhập tên mẫu:")
        if name:
            subject = self.entry_subject.get().strip()
            body = self.text_body.get("1.0", tk.END).strip()
            use_html = self.var_html.get()
            self.templates[name] = {"subject": subject, "body": body, "html": use_html}
            self.save_templates()
            self.update_template_list()
            self.add_auto_log(f"Đã lưu mẫu: {name}")

    def delete_template(self):
        name = self.current_template.get()
        if name and name in self.templates:
            if messagebox.askyesno("Xóa mẫu", f"Xóa mẫu '{name}'?"):
                del self.templates[name]
                self.save_templates()
                self.update_template_list()
                self.add_auto_log(f"Đã xóa mẫu: {name}")

    def load_template(self, event=None):
        name = self.current_template.get()
        if name and name in self.templates:
            tpl = self.templates[name]
            self.entry_subject.delete(0, tk.END)
            self.entry_subject.insert(0, tpl["subject"])
            self.text_body.delete("1.0", tk.END)
            self.text_body.insert("1.0", tpl["body"])
            self.var_html.set(tpl.get("html", False))
            self.add_auto_log(f"Đã tải mẫu: {name}")

    def update_template_list(self):
        names = list(self.templates.keys())
        self.template_combo['values'] = names
        if names:
            self.template_combo.set(names[0])
        else:
            self.template_combo.set("")

    def load_merge_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("CSV files", "*.csv")])
        if file_path:
            self.merge_fields_file.set(file_path)
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    reader = csv.DictReader(f)
                    self.merge_headers = reader.fieldnames
                    self.merge_data = list(reader)
                preview = f"Headers: {', '.join(self.merge_headers)}\n"
                if self.merge_data:
                    preview += f"Mẫu: {self.merge_data[0]}"
                else:
                    preview += "Không có dữ liệu."
                self.merge_preview.config(state=tk.NORMAL)
                self.merge_preview.delete("1.0", tk.END)
                self.merge_preview.insert("1.0", preview)
                self.merge_preview.config(state=tk.DISABLED)
                self.add_auto_log(f"Đã tải file merge: {file_path}, {len(self.merge_data)} dòng")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể đọc file CSV: {e}")

    def apply_merge_fields(self, text, row):
        for field, value in row.items():
            text = text.replace(f"{{{field}}}", str(value))
        return text

    def check_mx_record(self, email):
        if not self.enable_mx_validation.get() or not MX_AVAILABLE:
            return True
        domain = email.split('@')[-1]
        try:
            dns.resolver.resolve(domain, 'MX')
            return True
        except:
            return False

    def export_stats(self):
        if not self.accounts:
            messagebox.showwarning("Không có dữ liệu", "Không có tài khoản nào để xuất.")
            return
        file_path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV files", "*.csv")])
        if file_path:
            try:
                with open(file_path, 'w', newline='', encoding='utf-8') as f:
                    writer = csv.writer(f)
                    writer.writerow(["Email", "Tổng gửi", "Thành công", "Lỗi", "Trạng thái"])
                    for acc in self.accounts:
                        writer.writerow([acc['email'], acc['sent'], acc['success'], acc['error'], acc['status']])
                messagebox.showinfo("Thành công", f"Đã xuất thống kê ra file:\n{file_path}")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể ghi file: {e}")

    # Anti-spam functions
    def browse_anti_subject_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if file_path:
            self.anti_subject_file.set(file_path)
            self.add_auto_log(f"Đã chọn file chủ đề ngẫu nhiên: {file_path}")

    def browse_anti_body_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt"), ("HTML files", "*.html")])
        if file_path:
            self.anti_body_file.set(file_path)
            self.add_auto_log(f"Đã chọn file nội dung ngẫu nhiên: {file_path}")

    def browse_anti_signature_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if file_path:
            self.anti_signature_file.set(file_path)
            self.add_auto_log(f"Đã chọn file chữ ký ngẫu nhiên: {file_path}")

    def browse_anti_sender_names_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if file_path:
            self.anti_sender_names_file.set(file_path)
            self.add_auto_log(f"Đã chọn file tên hiển thị: {file_path}")

    def browse_anti_attachment_folder(self):
        folder_path = filedialog.askdirectory()
        if folder_path:
            self.anti_attachment_folder.set(folder_path)
            self.add_auto_log(f"Đã chọn thư mục file đính kèm: {folder_path}")

    def get_random_delay(self, base_delay):
        delay = base_delay
        if self.anti_random_delay.get():
            min_d = self.anti_delay_min.get()
            max_d = self.anti_delay_max.get()
            if min_d <= max_d:
                delay = random.uniform(min_d, max_d)
        if self.anti_jitter.get():
            jitter_pct = self.anti_jitter_percent.get() / 100.0
            delay = delay * (1 + random.uniform(-jitter_pct, jitter_pct))
            delay = max(0.1, delay)
        return delay

    def get_random_subject(self, default_subject):
        if self.anti_random_subject.get() and self.anti_subject_file.get():
            try:
                with open(self.anti_subject_file.get(), 'r', encoding='utf-8') as f:
                    subjects = [line.strip() for line in f if line.strip()]
                if subjects:
                    return random.choice(subjects)
            except Exception as e:
                self.add_auto_log(f"Lỗi đọc file chủ đề ngẫu nhiên: {e}")
        return default_subject

    def get_random_body(self, default_body):
        if self.anti_random_body.get() and self.anti_body_file.get():
            try:
                with open(self.anti_body_file.get(), 'r', encoding='utf-8') as f:
                    bodies = [line.strip() for line in f if line.strip()]
                if bodies:
                    return random.choice(bodies)
            except Exception as e:
                self.add_auto_log(f"Lỗi đọc file nội dung ngẫu nhiên: {e}")
        return default_body

    def add_random_signature(self, body):
        if self.anti_random_signature.get() and self.anti_signature_file.get():
            try:
                with open(self.anti_signature_file.get(), 'r', encoding='utf-8') as f:
                    signatures = [line.strip() for line in f if line.strip()]
                if signatures:
                    sig = random.choice(signatures)
                    return body + "\n\n-- \n" + sig
            except Exception as e:
                self.add_auto_log(f"Lỗi đọc file chữ ký: {e}")
        return body

    def get_random_sender_name(self, email):
        if self.anti_random_sender_name.get() and self.anti_sender_names_file.get():
            try:
                with open(self.anti_sender_names_file.get(), 'r', encoding='utf-8') as f:
                    names = [line.strip() for line in f if line.strip()]
                if names:
                    name = random.choice(names)
                    return formataddr((name, email))
            except Exception as e:
                self.add_auto_log(f"Lỗi đọc file tên hiển thị: {e}")
        return email

    def get_random_attachment(self):
        if self.anti_random_attachment.get() and self.anti_attachment_folder.get():
            folder = self.anti_attachment_folder.get()
            try:
                files = [os.path.join(folder, f) for f in os.listdir(folder)
                         if os.path.isfile(os.path.join(folder, f))]
                if files:
                    return random.choice(files)
            except Exception as e:
                self.add_auto_log(f"Lỗi đọc thư mục file đính kèm: {e}")
        return None

    def get_random_header(self):
        if self.anti_random_headers.get():
            mailers = [
                "Microsoft Outlook 16.0",
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                "Apple Mail (2.3608.120.23.2.1)",
                "Gmail SMTP",
                "Thunderbird 91.0",
                "Mailspring 1.10.0"
            ]
            return random.choice(mailers)
        return "Gmail SMTP Pro"

    def should_use_html(self, default_use_html):
        if self.anti_random_html.get():
            return random.choice([True, False])
        return default_use_html

    def shuffle_emails(self, emails):
        if self.anti_shuffle_emails.get():
            shuffled = emails.copy()
            random.shuffle(shuffled)
            return shuffled
        return emails

    def add_hidden_content(self, body):
        if not self.anti_hidden_content.get():
            return body
        hidden = '<span style="color:#ffffff; font-size:0px; display:none;">' + \
                 ''.join(random.choices('abcdefghijklmnopqrstuvwxyz ', k=50)) + '</span>'
        return body + hidden

    def obfuscate_text(self, text):
        if not self.anti_obfuscate_chars.get():
            return text
        replacements = {
            'a': 'а', 'c': 'с', 'e': 'е', 'o': 'о', 'p': 'р', 'x': 'х', 'y': 'у'
        }
        chars = list(text)
        for i in range(len(chars)):
            if random.random() < 0.05 and chars[i].lower() in replacements:
                if chars[i].isupper():
                    chars[i] = replacements[chars[i].lower()].upper()
                else:
                    chars[i] = replacements[chars[i].lower()]
        return ''.join(chars)

    def rotate_proxy(self, on_error=False):
        if not self.anti_rotate_proxy.get():
            return
        if on_error and not self.anti_proxy_rotate_on_error.get():
            return
        if self.proxy_list:
            self.current_proxy_index = (self.current_proxy_index + 1) % len(self.proxy_list)
            proxy = self.proxy_list[self.current_proxy_index]
            self.root.after(0, lambda: self.proxy_address.set(f"{proxy[0]}:{proxy[1]}"))
            if proxy[2] and proxy[3]:
                self.root.after(0, lambda: self.proxy_username.set(proxy[2]))
                self.root.after(0, lambda: self.proxy_password.set(proxy[3]))
            else:
                self.root.after(0, lambda: self.proxy_username.set(""))
                self.root.after(0, lambda: self.proxy_password.set(""))
            if self.enable_detailed_log.get():
                self.add_auto_log(f"Đã chuyển sang proxy: {proxy[0]}:{proxy[1]}")

    # ==================== CÁC HÀM XỬ LÝ CHÍNH ====================
    def toggle_proxy_fields(self):
        state = "normal" if self.use_proxy.get() else "disabled"
        self.entry_proxy_addr.config(state=state)
        self.entry_proxy_user.config(state=state)
        self.entry_proxy_pass.config(state=state)
        self.proxy_type_combo.config(state="readonly" if self.use_proxy.get() else "disabled")

    def load_proxy_from_file_dialog(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if not file_path:
            return
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = [line.strip() for line in f if line.strip() and not line.startswith('#')]
            if not lines:
                messagebox.showinfo("Thông báo", "File không có proxy hợp lệ.")
                return
            proxy_win = tk.Toplevel(self.root)
            proxy_win.title("Chọn proxy")
            proxy_win.geometry("400x300")
            listbox = tk.Listbox(proxy_win, selectmode=tk.SINGLE)
            listbox.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
            for line in lines:
                listbox.insert(tk.END, line)
            def select_proxy():
                sel = listbox.curselection()
                if sel:
                    line = listbox.get(sel[0])
                    parts = line.split(':')
                    if len(parts) >= 2:
                        ip_port = f"{parts[0]}:{parts[1]}"
                        self.proxy_address.set(ip_port)
                        if len(parts) >= 4:
                            self.proxy_username.set(parts[2])
                            self.proxy_password.set(parts[3])
                        else:
                            self.proxy_username.set("")
                            self.proxy_password.set("")
                    proxy_win.destroy()
            btn_ok = tk.Button(proxy_win, text="Chọn", command=select_proxy)
            btn_ok.pack(pady=5)
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể đọc file: {e}")

    def update_account_list(self):
        for row in self.tree_accounts.get_children():
            self.tree_accounts.delete(row)
        for acc in self.accounts:
            self.tree_accounts.insert("", tk.END, values=(
                acc['email'],
                acc.get('sent', 0),
                acc.get('success', 0),
                acc.get('error', 0),
                acc.get('status', 'Chưa dùng')
            ))
        account_names = [f"{acc['email']}" for acc in self.accounts]
        self.account_combo['values'] = account_names
        if self.accounts:
            self.account_combo.current(0)
            self.on_account_selected(None)
        else:
            self.account_combo.set('')
            self.lbl_from.config(text="")
            self.btn_single.config(state=tk.DISABLED)
            self.btn_list.config(state=tk.DISABLED)

        # Cập nhật listbox chọn tài khoản auto
        self.auto_accounts_listbox.delete(0, tk.END)
        for acc in self.accounts:
            self.auto_accounts_listbox.insert(tk.END, acc['email'])

    def on_account_selected(self, event):
        selection = self.account_combo.get()
        if selection:
            for acc in self.accounts:
                if acc['email'] == selection:
                    self.current_account = acc
                    self.lbl_from.config(text=f"✓ {acc['email']}", fg="green")
                    self.btn_single.config(state=tk.NORMAL)
                    self.btn_list.config(state=tk.NORMAL)
                    break
        else:
            self.current_account = None
            self.lbl_from.config(text="")
            self.btn_single.config(state=tk.DISABLED)
            self.btn_list.config(state=tk.DISABLED)

    def import_accounts_from_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if not file_path:
            return
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = [line.strip() for line in f if line.strip() and ':' in line and not line.startswith('#')]
            new_count = 0
            for line in lines:
                email, password = line.split(':', 1)
                email = email.strip()
                password = password.strip()
                if any(acc['email'] == email for acc in self.accounts):
                    continue
                new_acc = {
                    'email': email,
                    'password': password,
                    'sent': 0,
                    'success': 0,
                    'error': 0,
                    'status': 'Chưa dùng'
                }
                self.accounts.append(new_acc)
                new_count += 1
            if new_count > 0:
                self.save_accounts()
                self.update_account_list()
                messagebox.showinfo("Thành công", f"Đã nhập {new_count} tài khoản mới.")
            else:
                messagebox.showinfo("Không có tài khoản mới", "Không tìm thấy tài khoản hợp lệ hoặc tất cả đã tồn tại.")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể đọc file: {e}")

    def export_accounts_to_file(self):
        if not self.accounts:
            messagebox.showwarning("Không có tài khoản", "Không có tài khoản nào để xuất.")
            return
        file_path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text files", "*.txt")])
        if not file_path:
            return
        try:
            with open(file_path, 'w', encoding='utf-8') as f:
                for acc in self.accounts:
                    f.write(f"{acc['email']}:{acc['password']}\n")
            messagebox.showinfo("Thành công", f"Đã xuất {len(self.accounts)} tài khoản ra file.")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể ghi file: {e}")

    def add_account(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Thêm tài khoản Gmail")
        dialog.geometry("400x200")
        dialog.resizable(False, False)

        tk.Label(dialog, text="Email Gmail:").grid(row=0, column=0, padx=10, pady=10, sticky="w")
        entry_email = tk.Entry(dialog, width=40)
        entry_email.grid(row=0, column=1, padx=10, pady=10)

        tk.Label(dialog, text="Mật khẩu ứng dụng:").grid(row=1, column=0, padx=10, pady=10, sticky="w")
        entry_password = tk.Entry(dialog, width=40, show="*")
        entry_password.grid(row=1, column=1, padx=10, pady=10)

        def save_account():
            email = entry_email.get().strip()
            password = entry_password.get()
            if not email or not password:
                messagebox.showwarning("Thiếu thông tin", "Vui lòng nhập đầy đủ email và mật khẩu")
                return
            for acc in self.accounts:
                if acc['email'] == email:
                    messagebox.showwarning("Trùng lặp", f"Tài khoản {email} đã tồn tại!")
                    return
            new_acc = {
                'email': email,
                'password': password,
                'sent': 0,
                'success': 0,
                'error': 0,
                'status': 'Chưa dùng'
            }
            self.accounts.append(new_acc)
            self.save_accounts()
            self.update_account_list()
            dialog.destroy()
            messagebox.showinfo("Thành công", f"Đã thêm tài khoản {email}")

        tk.Button(dialog, text="Lưu", command=save_account, bg="#4CAF50", fg="white").grid(row=2, column=0, columnspan=2, pady=20)

    def edit_account(self):
        if not self.current_account:
            messagebox.showwarning("Chưa chọn", "Vui lòng chọn tài khoản cần sửa")
            return

        dialog = tk.Toplevel(self.root)
        dialog.title("Sửa tài khoản Gmail")
        dialog.geometry("400x200")
        dialog.resizable(False, False)

        tk.Label(dialog, text="Email Gmail:").grid(row=0, column=0, padx=10, pady=10, sticky="w")
        entry_email = tk.Entry(dialog, width=40)
        entry_email.insert(0, self.current_account['email'])
        entry_email.config(state="readonly")
        entry_email.grid(row=0, column=1, padx=10, pady=10)

        tk.Label(dialog, text="Mật khẩu ứng dụng:").grid(row=1, column=0, padx=10, pady=10, sticky="w")
        entry_password = tk.Entry(dialog, width=40, show="*")
        entry_password.insert(0, self.current_account['password'])
        entry_password.grid(row=1, column=1, padx=10, pady=10)

        def save_account():
            new_password = entry_password.get()
            if not new_password:
                messagebox.showwarning("Thiếu thông tin", "Vui lòng nhập mật khẩu")
                return
            for acc in self.accounts:
                if acc['email'] == self.current_account['email']:
                    acc['password'] = new_password
                    break
            self.save_accounts()
            self.current_account['password'] = new_password
            self.update_account_list()
            dialog.destroy()
            messagebox.showinfo("Thành công", f"Đã cập nhật mật khẩu cho {self.current_account['email']}")

        tk.Button(dialog, text="Cập nhật", command=save_account, bg="#FF9800", fg="white").grid(row=2, column=0, columnspan=2, pady=20)

    def delete_account(self):
        if not self.current_account:
            messagebox.showwarning("Chưa chọn", "Vui lòng chọn tài khoản cần xóa")
            return
        if messagebox.askyesno("Xác nhận", f"Bạn có chắc muốn xóa tài khoản {self.current_account['email']}?"):
            self.accounts = [acc for acc in self.accounts if acc['email'] != self.current_account['email']]
            self.save_accounts()
            self.update_account_list()
            messagebox.showinfo("Thành công", "Đã xóa tài khoản")

    def reset_stats(self):
        for acc in self.accounts:
            acc['sent'] = 0
            acc['success'] = 0
            acc['error'] = 0
            acc['status'] = 'Chưa dùng'
        self.save_accounts()
        self.update_account_list()
        messagebox.showinfo("Thành công", "Đã reset thống kê cho tất cả tài khoản")

    def load_recipient_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    emails = [line.strip() for line in f if line.strip()]
                self.recipient_list = emails
                self.recipient_listbox.delete(0, tk.END)
                for email in emails:
                    self.recipient_listbox.insert(tk.END, email)
                self.lbl_recipient_count.config(text=f"{len(emails)} email")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể đọc file: {e}")

    def add_attachment(self):
        files = filedialog.askopenfilenames(title="Chọn file đính kèm")
        for f in files:
            if f not in self.attachments:
                self.attachments.append(f)
                self.attach_listbox.insert(tk.END, os.path.basename(f))

    def remove_attachment(self):
        selection = self.attach_listbox.curselection()
        if selection:
            index = selection[0]
            self.attach_listbox.delete(index)
            del self.attachments[index]

    def remove_all_attachments(self):
        if self.attachments:
            self.attachments.clear()
            self.attach_listbox.delete(0, tk.END)
            self.add_auto_log("Đã xóa tất cả file đính kèm")
        else:
            messagebox.showinfo("Thông báo", "Không có file đính kèm nào")

    def clear_recipient_list(self):
        self.recipient_list = []
        self.recipient_listbox.delete(0, tk.END)
        self.lbl_recipient_count.config(text="")
        self.add_auto_log("Đã xóa danh sách email")

    def deduplicate_emails(self):
        if not self.recipient_list:
            messagebox.showinfo("Thông báo", "Danh sách email trống")
            return
        original_count = len(self.recipient_list)
        unique_emails = list(dict.fromkeys(self.recipient_list))
        duplicate_count = original_count - len(unique_emails)
        if duplicate_count > 0:
            self.recipient_list = unique_emails
            self.recipient_listbox.delete(0, tk.END)
            for email in unique_emails:
                self.recipient_listbox.insert(tk.END, email)
            self.lbl_recipient_count.config(text=f"{len(unique_emails)} email (đã lọc {duplicate_count} trùng)")
            self.add_auto_log(f"Đã lọc {duplicate_count} email trùng, còn {len(unique_emails)} email")
        else:
            messagebox.showinfo("Thông báo", "Không có email trùng lặp")

    def validate_email_format(self, email):
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        return re.match(pattern, email) is not None

    def validate_emails(self):
        if not self.recipient_list:
            messagebox.showinfo("Thông báo", "Danh sách email trống")
            return
        valid_emails = []
        invalid_emails = []
        for email in self.recipient_list:
            if self.validate_email_format(email):
                valid_emails.append(email)
            else:
                invalid_emails.append(email)
        if invalid_emails:
            result = f"✅ Email hợp lệ: {len(valid_emails)}\n❌ Email không hợp lệ: {len(invalid_emails)}\n\nDanh sách email không hợp lệ:\n" + "\n".join(invalid_emails[:10])
            if len(invalid_emails) > 10:
                result += f"\n... và {len(invalid_emails)-10} email khác"
            messagebox.showwarning("Kết quả kiểm tra", result)
        else:
            messagebox.showinfo("Kết quả kiểm tra", f"✅ Tất cả {len(valid_emails)} email đều hợp lệ!")
        self.add_auto_log(f"Đã kiểm tra {len(self.recipient_list)} email: {len(valid_emails)} hợp lệ, {len(invalid_emails)} không hợp lệ")

    def save_content_to_file(self):
        subject = self.entry_subject.get().strip()
        body = self.text_body.get("1.0", tk.END).strip()
        if not subject and not body:
            messagebox.showwarning("Cảnh báo", "Không có nội dung để lưu")
            return
        file_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("HTML files", "*.html"), ("All files", "*.*")],
            title="Lưu nội dung email"
        )
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(f"SUBJECT:\n{subject}\n\nBODY:\n{body}")
                messagebox.showinfo("Thành công", f"Đã lưu nội dung vào file:\n{file_path}")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể lưu file: {e}")

    def load_content_from_file(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Text files", "*.txt"), ("HTML files", "*.html"), ("All files", "*.*")],
            title="Chọn file nội dung email"
        )
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                if "SUBJECT:" in content and "BODY:" in content:
                    subject_part = content.split("BODY:")[0].replace("SUBJECT:", "").strip()
                    body_part = content.split("BODY:")[1].strip()
                    self.entry_subject.delete(0, tk.END)
                    self.entry_subject.insert(0, subject_part)
                    self.text_body.delete("1.0", tk.END)
                    self.text_body.insert("1.0", body_part)
                else:
                    self.text_body.delete("1.0", tk.END)
                    self.text_body.insert("1.0", content)
                messagebox.showinfo("Thành công", f"Đã tải nội dung từ file:\n{file_path}")
            except Exception as e:
                messagebox.showerror("Lỗi", f"Không thể đọc file: {e}")

    def preview_html(self):
        if not self.var_html.get():
            messagebox.showinfo("Thông báo", "Vui lòng chọn 'Gửi dạng HTML' để xem trước")
            return
        body = self.text_body.get("1.0", tk.END).strip()
        if not body:
            messagebox.showwarning("Cảnh báo", "Không có nội dung để xem trước")
            return
        preview_win = tk.Toplevel(self.root)
        preview_win.title("Xem trước HTML")
        preview_win.geometry("800x600")
        text_preview = scrolledtext.ScrolledText(preview_win, wrap=tk.WORD, font=("Courier", 10))
        text_preview.pack(fill=tk.BOTH, expand=True)
        text_preview.insert("1.0", body)
        text_preview.config(state=tk.DISABLED)
        info_label = tk.Label(preview_win, text="Đây là mã HTML thô. Khi gửi, email sẽ hiển thị dạng HTML.",
                              fg="blue", bg="yellow")
        info_label.pack(pady=5)

    def create_smtp_via_proxy(self):
        if self.use_proxy.get():
            proxy_addr = self.proxy_address.get().strip()
            if not proxy_addr:
                raise ValueError("Địa chỉ proxy không được để trống")
            try:
                if ':' in proxy_addr:
                    proxy_host, proxy_port = proxy_addr.split(':')
                    proxy_port = int(proxy_port)
                else:
                    raise ValueError("Định dạng proxy phải là ip:port")
            except:
                raise ValueError("Định dạng proxy không hợp lệ. Hãy dùng ip:port (ví dụ: 192.168.1.1:8080)")

            if self.custom_smtp.get():
                dest_host = self.smtp_host.get()
                dest_port = self.smtp_port.get()
                use_ssl = self.smtp_use_ssl.get()
            else:
                dest_host = "smtp.gmail.com"
                dest_port = 587
                use_ssl = False

            proxy_map = {"HTTP": socks.HTTP, "SOCKS4": socks.SOCKS4, "SOCKS5": socks.SOCKS5}
            proxy_type = proxy_map.get(self.proxy_type.get(), socks.SOCKS5)
            username = self.proxy_username.get().strip() or None
            password = self.proxy_password.get().strip() or None

            sock = socks.socksocket()
            sock.set_proxy(proxy_type, proxy_host, proxy_port, username=username, password=password)
            sock.connect((dest_host, dest_port))

            if use_ssl:
                import ssl
                context = ssl.create_default_context()
                server = smtplib.SMTP()
                server.sock = context.wrap_socket(sock, server_hostname=dest_host)
            else:
                server = smtplib.SMTP()
                server.sock = sock
                server.starttls()
            return server
        else:
            if self.custom_smtp.get():
                host = self.smtp_host.get()
                port = self.smtp_port.get()
                use_ssl = self.smtp_use_ssl.get()
                if use_ssl:
                    server = smtplib.SMTP_SSL(host, port)
                else:
                    server = smtplib.SMTP(host, port)
                    server.starttls()
                return server
            else:
                server = smtplib.SMTP("smtp.gmail.com", 587)
                server.starttls()
                return server

    def build_message(self, account_email, recipient, subject, body, use_html, attachments, merge_row=None):
        if merge_row:
            subject = self.apply_merge_fields(subject, merge_row)
            body = self.apply_merge_fields(body, merge_row)

        subject = self.get_random_subject(subject)
        body = self.get_random_body(body)
        body = self.add_random_signature(body)
        if use_html:
            body = self.add_hidden_content(body)
        else:
            body = self.obfuscate_text(body)
        use_html = self.should_use_html(use_html)
        sender_name = self.get_random_sender_name(account_email)

        msg = MIMEMultipart()
        msg["From"] = sender_name
        msg["To"] = recipient
        msg["Subject"] = subject
        msg["X-Mailer"] = self.get_random_header()

        content_type = "html" if use_html else "plain"
        msg.attach(MIMEText(body, content_type))

        all_attachments = list(attachments)
        if self.anti_random_attachment.get():
            rand_attach = self.get_random_attachment()
            if rand_attach and rand_attach not in all_attachments:
                all_attachments.append(rand_attach)

        for file_path in all_attachments:
            try:
                with open(file_path, "rb") as f:
                    part = MIMEBase("application", "octet-stream")
                    part.set_payload(f.read())
                encoders.encode_base64(part)
                part.add_header("Content-Disposition", f"attachment; filename= {os.path.basename(file_path)}")
                msg.attach(part)
            except Exception as e:
                raise Exception(f"Lỗi đính kèm file {file_path}: {e}")

        return msg

    def update_account_stats(self, account, sent=0, success=0, error=0, status=None):
        with self.file_lock:
            account['sent'] += sent
            account['success'] += success
            account['error'] += error
            if status:
                account['status'] = status
            self.save_accounts()
        self.root.after(0, self.update_account_list)

    # ==================== HÀM AI ====================
    def clear_ai_cache(self):
        """Xóa cache nội dung AI"""
        self.ai_content_cache.clear()
        self.add_auto_log("Đã xóa cache AI")
        messagebox.showinfo("Thành công", "Đã xóa cache nội dung AI")

    def generate_unique_content(self, recipient_email, index):
        """Tạo nội dung duy nhất cho mỗi email"""
        topic = self.ollama_topic.get().strip()
        tone = self.ollama_tone.get().strip()
        length = self.ollama_length.get().strip()
        language = self.ollama_language.get().strip()
        custom = self.ollama_custom_prompt.get().strip()

        # Tạo seed khác nhau cho mỗi email để có nội dung khác nhau
        seed = f"{recipient_email}_{index}_{int(time.time())}"
        seed_hash = hashlib.md5(seed.encode()).hexdigest()[:8]

        if custom:
            prompt = f"{custom}\n\nHãy viết nội dung khác biệt cho email này. Seed: {seed_hash}"
        else:
            prompt = f"""Viết một email về chủ đề: {topic}.
Phong cách: {tone}.
Độ dài: {length}.
Ngôn ngữ: {language}.
Đây là email thứ {index+1}, hãy viết nội dung khác với các email trước.
Chỉ viết nội dung email. Dòng đầu tiên là TIÊU ĐỀ, các dòng sau là NỘI DUNG.
Seed: {seed_hash}"""

        # Kiểm tra cache nếu bật
        if self.ai_cache_enabled.get():
            cache_key = hashlib.md5(prompt.encode()).hexdigest()
            if cache_key in self.ai_content_cache:
                self.add_auto_log(f"Dùng cache cho {recipient_email}")
                return self.ai_content_cache[cache_key]

        model = self.ollama_model.get().strip() or "tinyllama:1.1b"
        url = self.ollama_url.get().strip() or "http://localhost:11434/api/generate"

        for attempt in range(self.ai_max_retries.get()):
            try:
                payload = {
                    "model": model,
                    "prompt": prompt,
                    "stream": False,
                    "options": {"temperature": 0.8 + (attempt * 0.1), "num_predict": 400}
                }
                resp = requests.post(url, json=payload, timeout=60)
                if resp.status_code == 200:
                    data = resp.json()
                    text = data.get("response", "").strip()
                    if text:
                        # Lưu cache
                        if self.ai_cache_enabled.get():
                            cache_key = hashlib.md5(prompt.encode()).hexdigest()
                            self.ai_content_cache[cache_key] = text
                        return text
                time.sleep(1)
            except Exception as e:
                self.add_auto_log(f"Lỗi AI lần {attempt+1}: {e}")
                if attempt == self.ai_max_retries.get() - 1:
                    raise
                time.sleep(2)
        raise Exception("Không thể tạo nội dung sau nhiều lần thử")

    def generate_with_ollama(self):
        """Tạo một mẫu nội dung để test"""
        if not self.ollama_enabled.get():
            messagebox.showwarning("AI chưa bật", "Vui lòng bật AI Ollama trong tab Cài đặt")
            return

        self.add_auto_log("🔄 Đang tạo nội dung mẫu...")
        self.status_label.config(text="Đang sinh nội dung mẫu...", fg="blue")
        self.root.update()

        def call():
            try:
                text = self.generate_unique_content("test@example.com", 0)
                lines = text.split('\n')
                subject_line = lines[0].strip()
                if len(subject_line) > 100:
                    subject = subject_line[:97] + "..."
                    body_text = text
                else:
                    subject = subject_line
                    body_text = '\n'.join(lines[1:]).strip() or text
                self.root.after(0, lambda: self.entry_subject.delete(0, tk.END))
                self.root.after(0, lambda: self.entry_subject.insert(0, subject))
                self.root.after(0, lambda: self.text_body.delete("1.0", tk.END))
                self.root.after(0, lambda: self.text_body.insert("1.0", body_text))
                self.add_auto_log("✅ Đã tạo nội dung mẫu thành công")
                self.status_label.config(text="Đã sinh nội dung mẫu", fg="green")
                if self.enable_popup_notification.get():
                    messagebox.showinfo("AI Ollama", "Đã tạo nội dung mẫu thành công!")
            except Exception as e:
                err = f"Lỗi AI: {e}"
                self.add_auto_log(f"❌ {err}")
                self.root.after(0, lambda: self.status_label.config(text=err, fg="red"))
                messagebox.showerror("Lỗi AI", f"Không thể sinh nội dung:\n{err}\n\nKiểm tra Ollama đã chạy chưa?\nChạy: ollama serve")
        threading.Thread(target=call, daemon=True).start()

    # ==================== GỬI ĐƠN ====================
    def send_single_email(self):
        if not self.current_account:
            messagebox.showwarning("Chưa chọn tài khoản", "Vui lòng chọn tài khoản")
            return
        recipient = self.entry_to.get().strip()
        if not recipient:
            messagebox.showwarning("Thiếu thông tin", "Vui lòng nhập email người nhận")
            return

        # Nếu bật AI cho mỗi email, tạo nội dung mới
        if self.ai_per_email.get() and self.ollama_enabled.get():
            self.status_label.config(text="Đang tạo nội dung bằng AI...", fg="blue")
            self.root.update()
            try:
                content = self.generate_unique_content(recipient, 0)
                lines = content.split('\n')
                subject = lines[0].strip()
                if len(subject) > 100:
                    subject = subject[:97] + "..."
                body = '\n'.join(lines[1:]).strip() or content
            except Exception as e:
                messagebox.showerror("Lỗi AI", f"Không thể tạo nội dung:\n{e}")
                return
        else:
            subject = self.entry_subject.get().strip()
            body = self.text_body.get("1.0", tk.END).strip()
            if not subject or not body:
                messagebox.showwarning("Thiếu thông tin", "Vui lòng nhập chủ đề và nội dung")
                return

        use_html = self.var_html.get()

        if self.enable_mx_validation.get() and not self.check_mx_record(recipient):
            messagebox.showwarning("MX không hợp lệ", f"Domain {recipient.split('@')[-1]} không có MX record")
            return

        try:
            msg = self.build_message(self.current_account['email'], recipient, subject, body, use_html, self.attachments)
        except Exception as e:
            messagebox.showerror("Lỗi", str(e))
            return

        self.status_label.config(text="🔄 Đang gửi...", fg="blue")
        self.root.update()
        server = None
        try:
            server = self.create_smtp_via_proxy()
            server.login(self.current_account['email'], self.current_account['password'])
            server.send_message(msg)
            self.status_label.config(text="✅ Gửi thành công!", fg="green")
            self.update_account_stats(self.current_account, sent=1, success=1, status="Thành công")
            if self.enable_popup_notification.get():
                messagebox.showinfo("Thành công", "Email đã được gửi!")
        except Exception as e:
            self.status_label.config(text=f"❌ Lỗi: {str(e)}", fg="red")
            self.update_account_stats(self.current_account, sent=1, error=1, status="Lỗi")
            if self.enable_popup_notification.get():
                messagebox.showerror("Lỗi", f"Gửi email thất bại:\n{str(e)}")
        finally:
            if server:
                server.quit()

    # ==================== GỬI DANH SÁCH VỚI 1 TÀI KHOẢN ====================
    def send_to_list(self):
        if not self.current_account:
            messagebox.showwarning("Chưa chọn tài khoản", "Vui lòng chọn tài khoản")
            return
        if not self.recipient_list:
            messagebox.showwarning("Danh sách trống", "Vui lòng tải danh sách email trong Tab 2")
            return

        # Kiểm tra nội dung mẫu nếu không dùng AI
        if not self.ai_per_email.get() or not self.ollama_enabled.get():
            subject_master = self.entry_subject.get().strip()
            body_master = self.text_body.get("1.0", tk.END).strip()
            if not subject_master or not body_master:
                messagebox.showwarning("Thiếu thông tin", "Vui lòng nhập chủ đề và nội dung mẫu")
                return

        if self.enable_safe_mode.get():
            if not messagebox.askyesno("Xác nhận", f"Gửi {len(self.recipient_list)} email. Mỗi email sẽ có nội dung khác nhau. Tiếp tục?"):
                return

        recipients = self.shuffle_emails(self.recipient_list)

        self.sending_in_progress = True
        self.stop_sending = False
        self.btn_stop.config(state=tk.NORMAL)
        self.btn_single.config(state=tk.DISABLED)
        self.btn_list.config(state=tk.DISABLED)
        self.btn_all.config(state=tk.DISABLED)
        self.status_label.config(text="Đang gửi hàng loạt (mỗi email nội dung khác nhau)...", fg="blue")
        self.progress_bar['maximum'] = len(recipients)
        self.progress_bar['value'] = 0

        thread = threading.Thread(target=self.bulk_send_worker_ai, args=(recipients,))
        thread.daemon = True
        thread.start()

    def bulk_send_worker_ai(self, recipients):
        max_emails = self.max_emails.get()
        base_delay = self.delay_between.get()
        stop_on_error = self.stop_on_error.get()
        use_html = self.var_html.get()

        total = len(recipients)
        if max_emails > 0 and max_emails < total:
            recipients = recipients[:max_emails]
            total = len(recipients)

        success = 0
        error = 0

        for i, recipient in enumerate(recipients):
            if self.stop_sending:
                self.root.after(0, self.status_label.config, {"text": "Đã dừng"})
                break

            if self.enable_email_validation.get() and not self.validate_email_format(recipient):
                self.add_auto_log(f"Email không hợp lệ: {recipient}")
                error += 1
                if stop_on_error:
                    break
                continue

            if self.enable_mx_validation.get() and not self.check_mx_record(recipient):
                self.add_auto_log(f"MX không hợp lệ: {recipient}")
                error += 1
                if stop_on_error:
                    break
                continue

            # Tạo nội dung riêng cho mỗi email
            try:
                if self.ai_per_email.get() and self.ollama_enabled.get():
                    self.root.after(0, self.status_label.config, {"text": f"Đang tạo nội dung cho {recipient}..."})
                    content = self.generate_unique_content(recipient, i)
                    lines = content.split('\n')
                    subject = lines[0].strip()
                    if len(subject) > 100:
                        subject = subject[:97] + "..."
                    body = '\n'.join(lines[1:]).strip() or content
                    self.add_auto_log(f"Đã tạo nội dung AI cho {recipient}")
                else:
                    subject = self.entry_subject.get().strip()
                    body = self.text_body.get("1.0", tk.END).strip()
            except Exception as e:
                self.add_auto_log(f"Lỗi tạo nội dung cho {recipient}: {e}")
                error += 1
                if stop_on_error:
                    break
                continue

            merge_row = None
            if self.merge_data:
                merge_row = self.merge_data[i % len(self.merge_data)]

            try:
                msg = self.build_message(self.current_account['email'], recipient, subject, body, use_html, self.attachments, merge_row)
            except Exception as e:
                self.add_auto_log(f"Lỗi tạo email cho {recipient}: {e}")
                error += 1
                if stop_on_error:
                    break
                continue

            sent = False
            server = None
            for attempt in range(self.retry_on_error.get() + 1):
                if self.stop_sending:
                    break
                try:
                    server = self.create_smtp_via_proxy()
                    server.login(self.current_account['email'], self.current_account['password'])
                    server.send_message(msg)
                    sent = True
                    success += 1
                    self.root.after(0, self.progress_bar.config, {"value": i+1})
                    self.root.after(0, self.status_label.config, {"text": f"Đã gửi {success}/{total}"})
                    self.add_auto_log(f"✅ Gửi thành công đến {recipient} (nội dung cá nhân hóa)")
                    break
                except Exception as e:
                    if attempt < self.retry_on_error.get():
                        time.sleep(2)
                        if self.anti_rotate_proxy.get() and self.anti_proxy_rotate_on_error.get():
                            self.rotate_proxy(on_error=True)
                    else:
                        self.add_auto_log(f"❌ Lỗi gửi {recipient}: {e}")
                        error += 1
                        if stop_on_error:
                            self.stop_sending = True
                            break
                finally:
                    if server:
                        server.quit()

            if sent and not self.stop_sending:
                delay = self.get_random_delay(base_delay)
                time.sleep(delay)

        if self.enable_auto_save_stats.get():
            self.update_account_stats(self.current_account, sent=success+error, success=success, error=error,
                                      status="Hoàn tất" if not self.stop_sending else "Dừng")

        self.root.after(0, self.status_label.config, {"text": f"✅ Hoàn thành! {success}/{total} email."} if not self.stop_sending else f"⏹ Đã dừng sau {success} email.")

        if self.enable_popup_notification.get() and not self.stop_sending:
            messagebox.showinfo("Kết quả", f"Đã gửi thành công {success}/{total} email.\nMỗi email có nội dung khác nhau.\nLỗi: {error}")

        self.root.after(0, self.btn_stop.config, {"state": tk.DISABLED})
        self.root.after(0, self.btn_single.config, {"state": tk.NORMAL})
        self.root.after(0, self.btn_list.config, {"state": tk.NORMAL})
        self.root.after(0, self.btn_all.config, {"state": tk.NORMAL})
        self.sending_in_progress = False

    # ==================== GỬI VỚI TẤT CẢ TÀI KHOẢN ====================
    def send_to_all_accounts(self):
        if not self.recipient_list:
            messagebox.showwarning("Danh sách trống", "Vui lòng tải danh sách email")
            return
        if not self.accounts:
            messagebox.showwarning("Không có tài khoản", "Vui lòng thêm tài khoản")
            return

        if not self.ai_per_email.get() or not self.ollama_enabled.get():
            subject_master = self.entry_subject.get().strip()
            body_master = self.text_body.get("1.0", tk.END).strip()
            if not subject_master or not body_master:
                messagebox.showwarning("Thiếu thông tin", "Vui lòng nhập chủ đề và nội dung mẫu")
                return

        if self.enable_safe_mode.get():
            if not messagebox.askyesno("Xác nhận", f"Gửi {len(self.recipient_list)} email với {len(self.accounts)} tài khoản. Mỗi email nội dung khác nhau. Tiếp tục?"):
                return

        recipients = self.shuffle_emails(self.recipient_list)

        self.sending_in_progress = True
        self.multi_stop = False
        self.btn_stop.config(state=tk.NORMAL)
        self.btn_single.config(state=tk.DISABLED)
        self.btn_list.config(state=tk.DISABLED)
        self.btn_all.config(state=tk.DISABLED)
        self.status_label.config(text="Đang gửi với tất cả tài khoản (mỗi email nội dung khác nhau)...", fg="blue")
        self.multi_progress_bar['maximum'] = len(recipients)
        self.multi_progress_bar['value'] = 0

        thread = threading.Thread(target=self.multi_send_worker_main_ai, args=(recipients,))
        thread.daemon = True
        thread.start()

    def multi_send_worker_main_ai(self, recipients):
        max_emails = self.max_emails.get()
        if max_emails > 0 and max_emails < len(recipients):
            recipients = recipients[:max_emails]
        total = len(recipients)

        num_acc = len(self.accounts)
        chunk_size = (total + num_acc - 1) // num_acc
        chunks = [recipients[i:i+chunk_size] for i in range(0, total, chunk_size)]

        for acc in self.accounts:
            acc['last_batch_sent'] = 0

        threads = []
        for idx, acc in enumerate(self.accounts):
            if idx < len(chunks):
                chunk = chunks[idx]
            else:
                chunk = []
            if chunk:
                t = threading.Thread(target=self.multi_send_worker_single_ai, args=(acc, chunk, idx))
                t.daemon = True
                t.start()
                threads.append(t)

        while any(t.is_alive() for t in threads):
            total_sent = sum(acc.get('last_batch_sent', 0) for acc in self.accounts)
            self.root.after(0, self.multi_progress_bar.config, {"value": total_sent})
            self.root.after(0, self.multi_progress_label.config, {"text": f"Đã gửi {total_sent}/{total}"})
            time.sleep(0.5)

        self.root.after(0, self.multi_progress_label.config, {"text": "Hoàn tất"})
        self.root.after(0, self.status_label.config, {"text": "✅ Hoàn thành gửi với tất cả tài khoản"})
        self.root.after(0, self.btn_stop.config, {"state": tk.DISABLED})
        self.root.after(0, self.btn_single.config, {"state": tk.NORMAL})
        self.root.after(0, self.btn_list.config, {"state": tk.NORMAL})
        self.root.after(0, self.btn_all.config, {"state": tk.NORMAL})
        self.sending_in_progress = False

    def multi_send_worker_single_ai(self, account, recipients, acc_index):
        base_delay = self.delay_between.get()
        stop_on_error = self.stop_on_error.get()
        use_html = self.var_html.get()
        success = 0
        error = 0

        for idx, recipient in enumerate(recipients):
            if self.multi_stop:
                break

            if self.enable_email_validation.get() and not self.validate_email_format(recipient):
                self.add_auto_log(f"Email không hợp lệ: {recipient}")
                error += 1
                if stop_on_error:
                    break
                continue

            if self.enable_mx_validation.get() and not self.check_mx_record(recipient):
                self.add_auto_log(f"MX không hợp lệ: {recipient}")
                error += 1
                if stop_on_error:
                    break
                continue

            # Tạo nội dung riêng cho mỗi email
            try:
                if self.ai_per_email.get() and self.ollama_enabled.get():
                    content = self.generate_unique_content(recipient, idx + acc_index * 100)
                    lines = content.split('\n')
                    subject = lines[0].strip()
                    if len(subject) > 100:
                        subject = subject[:97] + "..."
                    body = '\n'.join(lines[1:]).strip() or content
                else:
                    subject = self.entry_subject.get().strip()
                    body = self.text_body.get("1.0", tk.END).strip()
            except Exception as e:
                self.add_auto_log(f"[{account['email']}] Lỗi tạo nội dung: {e}")
                error += 1
                if stop_on_error:
                    break
                continue

            merge_row = None
            if self.merge_data:
                merge_row = self.merge_data[idx % len(self.merge_data)]

            try:
                msg = self.build_message(account['email'], recipient, subject, body, use_html, self.attachments, merge_row)
            except Exception as e:
                self.add_auto_log(f"[{account['email']}] Lỗi tạo email: {e}")
                error += 1
                if stop_on_error:
                    break
                continue

            sent = False
            server = None
            for attempt in range(self.retry_on_error.get() + 1):
                if self.multi_stop:
                    break
                try:
                    server = self.create_smtp_via_proxy()
                    server.login(account['email'], account['password'])
                    server.send_message(msg)
                    sent = True
                    success += 1
                    account['last_batch_sent'] = account.get('last_batch_sent', 0) + 1
                    break
                except Exception as e:
                    if attempt < self.retry_on_error.get():
                        time.sleep(2)
                        if self.anti_rotate_proxy.get() and self.anti_proxy_rotate_on_error.get():
                            self.rotate_proxy(on_error=True)
                    else:
                        self.add_auto_log(f"[{account['email']}] Lỗi gửi {recipient}: {e}")
                        error += 1
                        if stop_on_error:
                            self.multi_stop = True
                            break
                finally:
                    if server:
                        server.quit()

            if sent and not self.multi_stop:
                time.sleep(self.get_random_delay(base_delay))

        if self.enable_auto_save_stats.get():
            self.update_account_stats(account, sent=success+error, success=success, error=error,
                                      status="Hoàn tất" if not self.multi_stop else "Dừng")

    def stop_sending(self):
        self.stop_sending = True
        self.multi_stop = True
        self.status_label.config(text="Đang dừng...")

    # ==================== AUTO ====================
    def browse_auto_email_list(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if file_path:
            self.auto_email_list_file.set(file_path)
            self.add_auto_log(f"Đã chọn file email: {file_path}")

    def browse_auto_subject(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt")])
        if file_path:
            self.auto_subject_file.set(file_path)
            self.add_auto_log(f"Đã chọn file chủ đề: {file_path}")

    def browse_auto_body(self):
        file_path = filedialog.askopenfilename(filetypes=[("Text files", "*.txt"), ("HTML files", "*.html")])
        if file_path:
            self.auto_body_file.set(file_path)
            self.add_auto_log(f"Đã chọn file nội dung: {file_path}")

    def add_auto_log(self, msg):
        self.root.after(0, lambda: self._add_auto_log(msg))

    def _add_auto_log(self, msg):
        self.auto_log.config(state=tk.NORMAL)
        self.auto_log.insert(tk.END, f"{time.strftime('%H:%M:%S')} - {msg}\n")
        self.auto_log.see(tk.END)
        self.auto_log.config(state=tk.DISABLED)

    def start_auto(self):
        if self.auto_running:
            messagebox.showwarning("Đang chạy", "Auto đang chạy")
            return
        if not self.auto_email_list_file.get():
            messagebox.showwarning("Thiếu file", "Vui lòng chọn file danh sách email")
            return
        selected = self.auto_accounts_listbox.curselection()
        if not selected:
            messagebox.showwarning("Chưa chọn tài khoản", "Chọn ít nhất một tài khoản")
            return
        self.auto_selected_accounts = [self.accounts[i] for i in selected]
        self.auto_stop = False
        self.auto_running = True
        self.btn_auto_start.config(state=tk.DISABLED)
        self.btn_auto_stop.config(state=tk.NORMAL)
        self.add_auto_log("===== BẮT ĐẦU AUTO =====")
        self.auto_thread = threading.Thread(target=self.auto_worker_ai)
        self.auto_thread.daemon = True
        self.auto_thread.start()

    def stop_auto(self):
        self.auto_stop = True
        self.add_auto_log("Đang dừng auto...")

    def auto_worker_ai(self):
        loop = 0
        max_loops = self.auto_loop_count.get() if not self.auto_loop_infinite.get() else None
        while not self.auto_stop:
            try:
                with open(self.auto_email_list_file.get(), 'r', encoding='utf-8') as f:
                    emails = [l.strip() for l in f if l.strip()]
                if not emails:
                    self.add_auto_log("File email rỗng")
                else:
                    self.add_auto_log(f"Đọc {len(emails)} email")
                    with open(self.auto_subject_file.get(), 'r', encoding='utf-8') as f:
                        subject = f.read().strip()
                    with open(self.auto_body_file.get(), 'r', encoding='utf-8') as f:
                        body = f.read().strip()
                    if not subject or not body:
                        self.add_auto_log("Chủ đề hoặc nội dung rỗng")
                    else:
                        self.add_auto_log(f"Đang gửi với {len(self.auto_selected_accounts)} tài khoản (mỗi email nội dung khác nhau)...")
                        self._auto_send_selected_accounts_ai(emails, subject, body, self.auto_use_html.get())
                        self.add_auto_log("Hoàn thành đợt")
            except Exception as e:
                self.add_auto_log(f"Lỗi: {e}")
            loop += 1
            if max_loops is not None and loop >= max_loops:
                self.add_auto_log(f"Đã đạt {max_loops} lần, dừng")
                break
            if not self.auto_stop:
                delay = self.auto_batch_delay.get()
                self.add_auto_log(f"Chờ {delay} giây...")
                for _ in range(int(delay)):
                    if self.auto_stop:
                        break
                    time.sleep(1)
        self.auto_running = False
        self.root.after(0, self.btn_auto_start.config, {"state": tk.NORMAL})
        self.root.after(0, self.btn_auto_stop.config, {"state": tk.DISABLED})
        self.add_auto_log("===== AUTO ĐÃ DỪNG =====")

    def _auto_send_selected_accounts_ai(self, recipients, master_subject, master_body, use_html):
        max_emails = self.max_emails.get()
        if max_emails > 0 and max_emails < len(recipients):
            recipients = recipients[:max_emails]
        total = len(recipients)
        num_acc = len(self.auto_selected_accounts)
        if num_acc == 0:
            return
        chunk_size = (total + num_acc - 1) // num_acc
        chunks = [recipients[i:i+chunk_size] for i in range(0, total, chunk_size)]
        threads = []
        for idx, acc in enumerate(self.auto_selected_accounts):
            if idx < len(chunks):
                chunk = chunks[idx]
            else:
                chunk = []
            if chunk:
                t = threading.Thread(target=self._auto_send_single_account_ai, args=(acc, chunk, master_subject, master_body, use_html, idx))
                t.daemon = True
                t.start()
                threads.append(t)
        for t in threads:
            t.join()

    def _auto_send_single_account_ai(self, account, recipients, master_subject, master_body, use_html, acc_offset):
        base_delay = self.delay_between.get()
        stop_on_error = self.stop_on_error.get()
        total = len(recipients)
        success = 0
        error = 0

        for i, recipient in enumerate(recipients):
            if self.auto_stop:
                break

            if self.enable_email_validation.get() and not self.validate_email_format(recipient):
                self.add_auto_log(f"[{account['email']}] Email không hợp lệ: {recipient}")
                error += 1
                if stop_on_error:
                    break
                continue

            if self.enable_mx_validation.get() and not self.check_mx_record(recipient):
                self.add_auto_log(f"[{account['email']}] MX không hợp lệ: {recipient}")
                error += 1
                if stop_on_error:
                    break
                continue

            # Tạo nội dung riêng cho mỗi email
            try:
                if self.ai_per_email.get() and self.ollama_enabled.get():
                    content = self.generate_unique_content(recipient, i + acc_offset * 100)
                    lines = content.split('\n')
                    subject = lines[0].strip()
                    if len(subject) > 100:
                        subject = subject[:97] + "..."
                    body = '\n'.join(lines[1:]).strip() or content
                else:
                    subject = master_subject
                    body = master_body
            except Exception as e:
                self.add_auto_log(f"[{account['email']}] Lỗi tạo nội dung: {e}")
                error += 1
                if stop_on_error:
                    break
                continue

            merge_row = None
            if self.merge_data:
                merge_row = self.merge_data[i % len(self.merge_data)]

            server = None
            try:
                msg = self.build_message(account['email'], recipient, subject, body, use_html, self.attachments, merge_row)
                server = self.create_smtp_via_proxy()
                server.login(account['email'], account['password'])
                server.send_message(msg)
                success += 1
                self.add_auto_log(f"[{account['email']}] ✅ Gửi thành công đến {recipient}")
                time.sleep(self.get_random_delay(base_delay))
            except Exception as e:
                self.add_auto_log(f"[{account['email']}] ❌ Lỗi gửi {recipient}: {e}")
                error += 1
                if stop_on_error:
                    break
            finally:
                if server:
                    server.quit()

        if self.enable_auto_save_stats.get():
            self.update_account_stats(account, sent=success+error, success=success, error=error, status="Auto")
        self.add_auto_log(f"[{account['email']}] Hoàn thành: {success}/{total} thành công")

    # ==================== GIAO DIỆN MÀU ====================
    def choose_bg_color(self):
        color = colorchooser.askcolor(title="Chọn màu nền", initialcolor=self.theme_bg.get())
        if color[1]:
            self.theme_bg.set(color[1])

    def choose_fg_color(self):
        color = colorchooser.askcolor(title="Chọn màu chữ", initialcolor=self.theme_fg.get())
        if color[1]:
            self.theme_fg.set(color[1])

    def choose_btn_color(self):
        color = colorchooser.askcolor(title="Chọn màu nút", initialcolor=self.theme_btn.get())
        if color[1]:
            self.theme_btn.set(color[1])

    def apply_theme(self):
        bg = self.theme_bg.get()
        fg = self.theme_fg.get()
        btn_bg = self.theme_btn.get()

        self.root.configure(bg=bg)
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('TNotebook', background=bg)
        style.configure('TNotebook.Tab', background=bg, foreground=fg)

        def apply_to_children(widget):
            try:
                if isinstance(widget, (tk.Frame, tk.LabelFrame, tk.Label, tk.Button, tk.Entry, tk.Text, tk.Listbox, scrolledtext.ScrolledText)):
                    widget.config(bg=bg, fg=fg)
                if isinstance(widget, tk.Button):
                    widget.config(bg=btn_bg, fg="white", activebackground=btn_bg)
                if isinstance(widget, tk.Entry):
                    widget.config(bg="white")
                if isinstance(widget, tk.Listbox):
                    widget.config(bg="white", fg=fg)
                if isinstance(widget, scrolledtext.ScrolledText):
                    widget.config(bg="white", fg=fg)
            except:
                pass
            for child in widget.winfo_children():
                apply_to_children(child)

        apply_to_children(self.root)
        self.save_settings()

if __name__ == "__main__":
    root = tk.Tk()
    app = EmailSenderApp(root)
    root.mainloop()