;;; isar-goal-mode.el --- Simple Isar Mode -*- lexical-binding: t -*-

;; Copyright (C) 2018-2020 Mathias Fleury
;; URL: https://bitbucket.org/zmaths/isabelle2019-vsce/

;; Keywords: lisp
;; Version: 0
;; Package-Requires: ((emacs "25.1") (isar-mode "0"))

;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and-or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

;;; Commentary:

;; blabla

;;; Code:

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
;;; isar-mode.el ends here