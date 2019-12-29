(require 'isar-mode)

(defvar isar-goal-mode-hook nil)

(defvar isar-goal-mode-map
  ()
  "Keymap for isar major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("*isar-output*" . isar-goal-mode))

(defvar isar-goal-most-outer-keyword
  (regexp-opt
   '("proof" "prove")))

(defvar isar-goal-outer-keyword
  (regexp-opt '("goal" "subgoal" "consts" "show") t))

(defvar isar-goal-inner-keyword
  "$^[:digit:]*.")

(defvar isar-goal-tactics ;; warning
  (regexp-opt '("Introduced" "fixed" "type" "variable" "variable(s)"
     "Ambiguous" "input""produces" "parse" "trees"
     "Ignoring" "duplicate" "rewrite" "rule" "introduction"
     "elim" "intro") t))

(defvar isar-goal-minor ;; information
  (regexp-opt '("is" "Found" "termination" "order" "Proofs" "for" "inductive" "predicate"
   "Successful" "attempt" "to" "solve" "goal" "by" "exported" "rule" "this" "calculation"
    "have" "using" "Proof" "outline" "with" "cases") t))

(defconst isar-goal-font-lock-keywords-1
  (list
   ;; (cons (concat "\\<" isar-goal-outer-keyword "\\>") 'font-lock-builtin-face)
   ;; 	(cons (concat "\\<" isar-goal-inner-keyword "\\>") 'font-lock-constant-face)
   ;; 	(cons (concat "\\<" isar-goal-tactics "\\>") 'font-lock-variable-name-face)
   ;; 	(cons (concat "\\<" isar-goal-most-outer-keyword "\\>") 'font-lock-preprocessor-face)
   ;; 	(cons (concat "\\<" isar-goal-minor "\\>") 'font-lock-type-face)
   ))


(defvar isar-goal-font-lock-keywords isar-goal-font-lock-keywords-1
  "Default highlighting expressions for isar mode")

(defvar isar-goal-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\" " " st)
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?\$ "." st)
    (modify-syntax-entry ?\/ "." st)
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?+  "." st)
    (modify-syntax-entry ?-  "." st)
    (modify-syntax-entry ?=  "." st)
    (modify-syntax-entry ?%  "." st)
    (modify-syntax-entry ?\& "." st)
    (modify-syntax-entry ?.  "w" st)
    ;;(modify-syntax-entry ?_  "w" st)
    (modify-syntax-entry ?\' "w" st)
    (modify-syntax-entry ??  "w" st)
    (modify-syntax-entry ?\( "()1" st)
    (modify-syntax-entry ?\) ")(4" st)
    (modify-syntax-entry ?\{ "(}1b" st)
    (modify-syntax-entry ?\} "){4b" st)
    (modify-syntax-entry ?\* ". 23n" st)
  st)
  "Syntax table for isar-goal-mode")

(defun isar-goal-mode ()
  "Major mode for editing isar files"
  (interactive)
  (kill-all-local-variables)
  (set-syntax-table isar-goal-mode-syntax-table)
  (use-local-map isar-goal-mode-map)
  (set (make-local-variable 'font-lock-defaults) '(isar-goal-font-lock-keywords))
  (unicode-tokens-configure)
  (setq major-mode 'isar-goal-mode)
  (setq isar-goal-name "isar-goal")
  (setq mode-name "Isar-goal")
  (unicode-tokens-mode 1)
  (run-hooks 'isar-goal-mode-hook))

;;spacemacs specific function
(setq spacemacs-jump-handlers-isar-goal-mode nil)

(provide 'isar-goal-mode)
