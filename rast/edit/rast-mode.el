;; load from your .emacs file
(setq auto-mode-alist
      (cons '("\\.rast$" . rast-mode) auto-mode-alist))

(defface font-lock-cost-face
  '((t :foreground "blue"))
  "rast cost model annotations"
  :group 'rast-mode)
(defvar font-lock-cost-face 'font-lock-cost-face)

(defface font-lock-time-face
  '((t :foreground "red"))
  "rast time actions"
  :group 'rast-mode)
(defvar font-lock-time-face 'font-lock-time-face)

(defface font-lock-work-face
  '((t :foreground "red"))
  "rast work actions"
  :group 'rast-mode)
(defvar font-lock-work-face 'font-lock-work-face)

(defface font-lock-constraints-face
  '((t :foreground "darkgreen"))
  "rast constraints"
  :group 'rast-mode)
(defvar font-lock-constraints-face 'font-lock-constraints-face)

(defface font-lock-decl-face
  '((t :foreground "purple"
       :weight bold))
  "face for declarations"
  :group 'rast-mode)
(defvar font-lock-decl-face 'font-lock-decl-face)

(defvar rast-font-lock-keywords
  '(("type\\|eqtype\\|decl\\|proc\\|exec" . font-lock-decl-face)
    ("case\\|wait\\|close\\|send\\|recv" . font-lock-keyword-face)
    ("tick\\|work" . font-lock-cost-face)
    ("pay\\|get" . font-lock-work-face)
    ("assert\\|assume\\|impossible" . font-lock-constraints-face)
    ("delay\\|when\\|now" . font-lock-time-face)
    ))

(setq rast-mode-syntax-table
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

(define-derived-mode rast-mode fundamental-mode "rast"
  "major mode for editing subsingleton code"
  (setq font-lock-defaults '(rast-font-lock-keywords))
  (set-syntax-table rast-mode-syntax-table))