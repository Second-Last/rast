;; load from your .emacs file
(setq auto-mode-alist
      (cons '("\\.ss$" . ss-mode) auto-mode-alist))

(defface font-lock-cost-face
  '((t :foreground "blue"))
  "ss cost model annotations"
  :group 'ss-mode)
(defvar font-lock-cost-face 'font-lock-cost-face)

(defface font-lock-time-face
  '((t :foreground "red"))
  "ss time actions"
  :group 'ss-mode)
(defvar font-lock-time-face 'font-lock-time-face)

(defface font-lock-work-face
  '((t :foreground "red"))
  "ss work actions"
  :group 'ss-mode)
(defvar font-lock-work-face 'font-lock-work-face)

(defface font-lock-constraints-face
  '((t :foreground "darkgreen"))
  "ss constraints"
  :group 'ss-mode)
(defvar font-lock-constraints-face 'font-lock-constraints-face)

(defface font-lock-decl-face
  '((t :foreground "purple"
       :weight bold))
  "face for declarations"
  :group 'ss-mode)
(defvar font-lock-decl-face 'font-lock-decl-face)

(defvar ss-font-lock-keywords
  '(("type\\|eqtype\\|decl\\|proc\\|exec" . font-lock-decl-face)
    ("<->\\|L\\.\\|R\\.\\|caseL\\|caseR\\|waitL\\|closeR" . font-lock-keyword-face)
    ("tick\\|work" . font-lock-cost-face)
    ("payR\\|payL\\|getR\\|getL" . font-lock-work-face)
    ("assertR\\|assertL\\|assumeR\\|assumeL\\|impossibleR\\|impossibleL" . font-lock-constraints-face)
    ("delay\\|whenL\\|whenR\\|nowL\\|nowR" . font-lock-time-face)
    ))

(setq ss-mode-syntax-table
  (let ((tbl (copy-syntax-table (standard-syntax-table))))
    (modify-syntax-entry ?# "<" tbl)
    (modify-syntax-entry ?\n ">" tbl)
    (modify-syntax-entry ?% "<" tbl)
    (modify-syntax-entry ?\( "()1" tbl)
    (modify-syntax-entry ?\* ". 23n" tbl)
    (modify-syntax-entry ?\) ")(4" tbl)
    (modify-syntax-entry ?' "_" tbl)
    (modify-syntax-entry ?_ "_" tbl)
    tbl))

(define-derived-mode ss-mode fundamental-mode "ss"
  "major mode for editing subsingleton code"
  (setq font-lock-defaults '(ss-font-lock-keywords))
  (set-syntax-table ss-mode-syntax-table))
