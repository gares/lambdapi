;;; lambdapi-smie.el --- Indentation for lambdapi -*- lexical-binding: t; -*-
;; SPDX-License-Identifier: CeCILL Free Software License Agreement v2.1
;;; Commentary:
;;
;;; Code:
(require 'lambdapi-vars)
(require 'smie)

;; Lists of keywords
(defconst lambdapi--tactics
  '("apply"
    "assume"
    "fail"
    "focus"
    "print"
    "proofterm"
    "refine"
    "reflexivity"
    "rewrite"
    "simpl"
    "symmetry"
    "why3"))
(defconst lambdapi--queries '("set" "assert" "assertnot" "type" "compute")
  "Commands that can appear in proofs.")
(defconst lambdapi--cmds
  (append '("symbol" "theorem" "rule" "and" "definition" "proof" "require")
          lambdapi--queries)
  "Commands at top level.")

(defun lambdapi--query-indent ()
  "Indent commands that may be in proofs.
Indent by `lambdapi-indent-basic' in proofs, and 0 otherwise."
  (save-excursion
    (forward-line -1)
    (back-to-indentation)
    (cond
     ((looking-at-p (regexp-opt (cons "proof" lambdapi--tactics)))
      `(column . ,lambdapi-indent-basic))
     ((looking-at-p (regexp-opt lambdapi--queries))
      ;; If the previous line is a query, indent similarly
      (back-to-indentation)
      `(column . ,(current-column)))
     (t '(column . 0)))))

(defconst lambdapi--smie-prec
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((ident)
      (env (ident)
           (csidentl ";" ident))
      (rw-patt)
      (args (ident)
            ("{" ident ":" sterm "}")
            ("(" ident ":" sterm ")"))
      (sterm ("TYPE")
             ("_")
             (ident)
             ("?" ident "[" env "]") ;; ?M[x;y;z]
             ("$" ident "[" env "]") ;; $X[x;y;z]
             (sterm "→" sterm)
             ("λ" args "," sterm)
             ("λ" ident ":" sterm "," sterm)
             ("Π" args "," sterm)
             ("Π" ident ":" sterm "," sterm)
             ("let" ident "≔" sterm "in" sterm)
             ("let" ident ":" sterm "≔" sterm "in" sterm)
             ("let" args ":" sterm "≔" sterm "in" sterm)
             ("let" args "≔" sterm "in" sterm))
      (tactic ("apply" sterm)
              ("assume" sterm)
              ("fail")
              ("focus" ident)
              ("print")
              ("proofterm")
              ("refine" sterm)
              ("reflexivity")
              ("rewrite" "[" rw-patt "]")
              ("simpl")
              ("why3"))
      (query ("assert" sterm ":" sterm)
             ("assert" sterm "≡" sterm)
             ("assertnot" sterm ":" sterm)
             ("assertnot" sterm "≡" sterm)
             ("compute" sterm)
             ("set" "debug" ident)
             ("set" "flag" ident "off")
             ("set" "flag" ident "on")
             ("set" "prover" ident)
             ("set" "prover_timeout" ident)
             ("set" "verbose" ident)
             ("type" sterm))
      (prfcontent (tactic)
                  (query))
      (unif-rule-rhs (sterm "≡" sterm)
                     (unif-rule-rhs ";" sterm "≡" sterm))
      (symdec ("symbol" args ":" sterm))
      (command ("constant" symdec)
               ("definition" args "≔" sterm)
               ("injective" symdec)
               ("open" ident)
               ("private" symdec)
               ("proof" prfcontent "abort")
               ("proof" prfcontent "admit")
               ("proof" prfcontent "qed")
               ("protected" symdec)
               ("require" ident "as" ident)
               ("require" ident)
               ("rule" sterm "↪" sterm)
               ("set" "builtin" ident "≔" sterm)
               ("set" "declared" ident)
               ("set" "infix" "left" ident "≔" sterm)
               ("set" "infix" "right" ident "≔" sterm)
               ("set" "infix" ident "≔" sterm)
               ("set" "prefix" ident "≔" sterm)
               ("set" "quantifier" ident)
               ("set" "unif_rule" sterm "≡" sterm "↪" unif-rule-rhs)
               ("theorem" args ":" sterm)
               ("with" sterm "↪" sterm)
               (symdec)))
    '((assoc "≡") (assoc ",") (assoc "in") (assoc "→")))))

(defun lambdapi--smie-forward-token ()
  "Forward lexer for Dedukti3."
  (smie-default-forward-token))

(defun lambdapi--smie-backward-token ()
  "Backward lexer for Dedukti3.
The default lexer is used because the syntax is primarily made of sexps."
  (smie-default-backward-token))

(defun lambdapi--smie-rules (kind token)
  "Indentation rule for case KIND and token TOKEN."
  (pcase (cons kind token)
    (`(:elem . basic) 0)

    (`(:list-intro . ,(or "require" "open")) t)
    (`(:after . ,(or "require" "open")) lambdapi-indent-basic)

    ;; tactics
    (`(:before . "simpl") `(column . ,lambdapi-indent-basic))
    (`(:before . "rewrite") `(column . ,lambdapi-indent-basic))
    (`(:before . "assume") `(column . ,lambdapi-indent-basic))
    (`(:before . "apply") `(column . ,lambdapi-indent-basic))
    (`(:before . "refine") `(column . ,lambdapi-indent-basic))
    (`(:before . "why3") `(column . ,lambdapi-indent-basic))
    (`(:before . "reflexivity") `(column . ,lambdapi-indent-basic))
    (`(:before . "focus") `(column . ,lambdapi-indent-basic))
    (`(:before . "print") `(column . ,lambdapi-indent-basic))
    (`(:before . "fail") `(column . ,lambdapi-indent-basic))

    (`(:before . ,(or "admit" "abort" "qed")) '(column . 0))
    (`(:after . ,(or "admit" "abort" "qed")) '(column . 0))

    (`(:before . ,(or "set" "compute" "type" "assert" "assertnot"))
     (lambdapi--query-indent))

    (`(,_ . ,(or "," "↪" "→" "≡")) (smie-rule-separator kind))

    (`(,(or :before :list-intro) . ,(or "≔" ":")) (smie-rule-separator kind))
    (`(:after . ,(or "≔" ":")) lambdapi-indent-basic)

    (`(:list-intro . ,(or "with" "rule" "λ" "Π" "proof")) t)
    (`(:after . "proof") lambdapi-indent-basic)
    (`(:after . ,(or "rule" "with")) (* 2 lambdapi-indent-basic))
    (`(:after . "in") (smie-rule-parent))
    (`(:after . ,(or "symbol" "definition" "theorem")) lambdapi-indent-basic)
    (`(:after . ,(or "simpl" "rewrite" "assume" "apply" "refine"
                     "why3" "reflexivity" "focus" "print" "fail"))
     lambdapi-indent-basic)

    ;; Toplevel
    (`(:before . "protected") '(column . 0))
    (`(:before . "private") '(column . 0))
    (`(:before . "injective") '(column . 0))
    (`(:before . "constant") '(column . 0))
    (`(:before . "require") '(column . 0))
    (`(:before . "open") '(column . 0))
    (`(:before . "definition") '(column . 0))
    (`(:before . "theorem") '(column . 0))
    (`(:before . "proof") '(column . 0))
    (`(:before . "symbol") '(column . 0))

    (`(:before . ,(or "with" "rule")) '(column . 0))))

(provide 'lambdapi-smie)
;;; lambdapi-smie.el ends here
