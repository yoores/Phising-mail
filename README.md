# Phising-mail
Tool này nhằm học tập tội sẽ không chịu tránh nhiệm 

liên hệ sửa lỗi qua @seraphin902

code full

# 🧰 1. Chức năng chính

👉 Gửi email tự động:

* Gửi **1 email đơn**
* Gửi **danh sách email**
* Gửi bằng **nhiều tài khoản cùng lúc**
* Có thể chạy **auto gửi liên tục**

---

# 📧 2. Quản lý tài khoản email

* Thêm / sửa / xóa tài khoản Gmail
* Import / export danh sách tài khoản
* Theo dõi:

  * Số mail đã gửi
  * Thành công / lỗi
* Test kết nối SMTP

---

# 👥 3. Quản lý người nhận

* Nhập email thủ công
* Load file danh sách (.txt)
* Lọc:

  * Email trùng
  * Email sai định dạng
* Có thể kiểm tra MX (domain mail tồn tại hay không)

---

# 📝 4. Soạn nội dung email

* Nhập:

  * Chủ đề
  * Nội dung
* Hỗ trợ:

  * HTML hoặc text
  * File đính kèm
* Lưu / load mẫu email (template)

---

# 🤖 5. AI tạo nội dung (Ollama + TinyLlama)

* Tự động tạo nội dung email bằng AI
* Tuỳ chỉnh:

  * Chủ đề (bán hàng, tuyển dụng…)
  * Giọng văn (chuyên nghiệp, hài hước…)
  * Độ dài
  * Ngôn ngữ
* Có thể:

  * 👉 Mỗi email nội dung khác nhau
  * 👉 Tránh bị spam filter

---

# 🛡️ 6. Anti-spam / né block

Rất nhiều tính năng “lách spam”:

* Delay ngẫu nhiên giữa các mail
* Random:

  * Chủ đề
  * Nội dung
  * chữ ký
  * tên người gửi
* Xáo trộn danh sách email
* Gửi theo batch ngẫu nhiên
* Thay đổi header email
* Ẩn nội dung HTML
* Obfuscate ký tự

👉 Mục đích: tránh bị Gmail/Outlook chặn

---

# 🌐 7. Proxy

* Hỗ trợ:

  * HTTP / SOCKS4 / SOCKS5
* Có thể:

  * Load list proxy
  * Xoay proxy mỗi email
  * Đổi proxy khi lỗi

---

# ⚙️ 8. Cài đặt nâng cao

* SMTP custom (không dùng Gmail)
* Gửi song song nhiều luồng
* Retry khi lỗi
* Giới hạn số email
* Delay giữa các batch

---

# 🤖 9. Auto gửi

* Chạy tự động theo:

  * File email
  * File nội dung
* Loop:

  * Lặp vô hạn hoặc số lần cố định
* Delay giữa mỗi vòng

---

# 📊 10. Thống kê & log

* Hiển thị log chi tiết
* Progress bar
* Xuất file CSV thống kê
