;;;; run-tests.scm --- Deterministic SRFI-64 tests for Deducto

(use-modules (srfi srfi-11)
             (srfi srfi-13)
             (srfi srfi-64)
             (deducto formulas)
             (deducto proof)
             (deducto check)
             (deducto hint)
             (deducto repl))

(define (read-proof-file path)
  (call-with-input-file path
    (lambda (port)
      (parse-proof (read port)))))

(define (check-file path)
  (let-values (((lines spans) (read-proof-file path)))
    (check-proof lines spans)))

(test-begin "deducto")

(test-assert "propositional atoms are valid"
             (valid-formula? 'P))
(test-assert "predicate formulas are valid"
             (valid-formula? '(Human Ada)))
(test-assert "quantifiers bind one variable"
             (valid-formula? '(forall (x) (Human x))))
(test-assert "false is not a term"
             (not (term? 'false)))
(test-assert "quantifiers reject multiple binders"
             (not (valid-formula? '(forall (x y) (Human x)))))
(test-equal "free variables respect binders"
            '(x)
            (free-vars '(forall (y) (and (Human x) (Human y)))))
(test-assert "substitution rejects capture"
             (not (substitute-free '(forall (y) (Knows x y)) 'x 'y)))

(test-assert "modus ponens proof is valid"
             (proof-result-ok?
              (check-file "proofs/valid/implication.scm")))
(test-assert "conjunction and disjunction rules are valid"
             (proof-result-ok?
              (check-file "proofs/valid/connectives.scm")))
(test-assert "negation rules and ex-falso are valid"
             (proof-result-ok?
              (check-file "proofs/valid/negation.scm")))
(test-assert "disjunction elimination is valid"
             (proof-result-ok?
              (check-file "proofs/valid/or-elim.scm")))
(test-assert "biconditional rules are valid"
             (proof-result-ok?
              (check-file "proofs/valid/iff.scm")))
(test-assert "subproof implication is valid"
             (proof-result-ok?
              (check-file "proofs/valid/subproof.scm")))
(test-assert "universal elimination and existential introduction are valid"
             (proof-result-ok?
              (check-file "proofs/valid/predicate.scm")))
(test-assert "universal introduction is valid"
             (proof-result-ok?
              (check-file "proofs/valid/forall-intro.scm")))
(test-assert "existential elimination is valid"
             (proof-result-ok?
              (check-file "proofs/valid/exists-elim.scm")))

(let ((result (check-file "proofs/invalid/wrong-repeat.scm")))
  (test-assert "wrong repeat is invalid"
               (not (proof-result-ok? result)))
  (test-equal "wrong repeat reports the first bad line"
              2
              (step-result-number (proof-result-first-failure result)))
  (test-assert "wrong repeat explains the rule"
               (string-contains
                (step-result-message (proof-result-first-failure result))
                "repeat")))

(let ((result (check-file "proofs/invalid/self-reference.scm")))
  (test-assert "self-reference is invalid"
               (not (proof-result-ok? result)))
  (test-assert "self-reference names the ordering error"
               (string-contains
                (step-result-message (proof-result-first-failure result))
                "earlier")))

(let ((result (check-file "proofs/invalid/unused-subproof.scm")))
  (test-assert "unused subproof is invalid"
               (not (proof-result-ok? result)))
  (test-assert "unused subproof is a global failure"
               (string-contains
                (step-result-message (proof-result-first-failure result))
                "never used")))

(let ((result (check-file "proofs/invalid/quantifier-fresh.scm")))
  (test-assert "quantifier freshness is checked"
               (not (proof-result-ok? result)))
  (test-assert "freshness reports the rule"
               (string-contains
                (step-result-message (proof-result-first-failure result))
                "forall-intro")))

(let-values (((lines spans) (read-proof-file "proofs/valid/subproof.scm")))
  (test-equal "proof format round trips"
              (read
               (open-input-string
                "(proof (subproof (P premise) (P repeat 1)) ((if P P) imp-intro (1 . 2)))"))
              (proof->spec lines spans)))

(test-assert "implication hint suggests introduction"
             (string-contains
              (hint-for '() '() '(if P Q))
              "imp-intro"))

(let ((line (make-line 1 0 '(Human Ada) 'premise '())))
  (test-assert "existential hint suggests a discovered witness"
               (string-contains
                (hint-for (list line)
                          '()
                          '(exists (x) (Human x)))
                "Ada")))

(let ((output (open-output-string)))
  (let-values (((lines spans level)
                (run-repl
                 (open-input-string
                  "(goal (if P P)) (open P) (step repeat P 1) (close imp-intro (if P P)) (check) (quit)")
                 output)))
    (test-equal "REPL closes all subproofs" 0 level)
    (test-assert "REPL builds a valid proof"
                 (proof-result-ok? (check-proof lines spans)))
    (test-assert "REPL reports success"
                 (string-contains (get-output-string output)
                                  "Result: valid."))))

(let ((output (open-output-string)))
  (run-repl
   (open-input-string "(premise P) (step repeat Q 1) (quit)")
   output)
  (test-assert "REPL reports an invalid line immediately"
               (string-contains (get-output-string output) "repeat")))

(test-end "deducto")

(exit (if (zero? (test-runner-fail-count (test-runner-current))) 0 1))