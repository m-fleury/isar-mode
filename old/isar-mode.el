(require 'isar-unicode-tokens)
(require 'unicode-tokens)
(require 'isar-syntax)

(defvar isar-mode-hook nil)

(defvar isar-mode-map
  (let ((map (make-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for isabelle major mode")

;; Autoload
(add-to-list 'auto-mode-alist '("\\.thy\\'" . isar-mode))

(defun unicode-tokens-configure ()
  "Set the Unicode Tokens table and initialise."
  (dolist (var unicode-tokens-configuration-variables)
    (if (boundp (intern (concat "isar-" (symbol-name var))))
        (set (intern (concat "unicode-tokens-" (symbol-name var) "-variable"))
             (intern (concat "isar-" (symbol-name var))))))
  (unicode-tokens-initialise))


(defconst isar-mode-font-lock-keywords
  (list
   (cons 'isar-match-nesting                               'font-lock-preprocessor-face)
   (cons (isar-ids-to-regexp isar-keywords-minor)          'font-lock-type-face)
   (cons (isar-ids-to-regexp isar-keywords-control)        'proof-error-face)
   (cons (isar-ids-to-regexp isar-keywords-diag)           'proof-tacticals-name-face)
   (cons (isar-ids-to-regexp isar-keywords-theory-enclose) 'font-lock-type-face)
   (cons (isar-ids-to-regexp isar-keywords-proper)         'font-lock-keyword-face)
   (cons (isar-ids-to-regexp isar-keywords-proof-context)  'proof-declaration-name-face)
   (cons (isar-ids-to-regexp isar-keywords-improper)       'font-lock-reference-face)
   (cons isar-improper-regexp 'font-lock-reference-face)
   (cons isar-antiq-regexp '(0 'font-lock-variable-name-face t))))


(define-derived-mode isar-mode fundamental-mode
  "isa Mode"
  "Major mode for isabelle files"
  (isar-init-syntax-table)
  (set (make-local-variable 'font-lock-defaults) '(isar-mode-font-lock-keywords))
  (unicode-tokens-configure)
  (unicode-tokens-mode 1)
  (setq major-mode 'isar-mode)
  (setq mode-name "isar")
  (run-hooks 'isar-mode-hook))


(provide 'isar-mode)
