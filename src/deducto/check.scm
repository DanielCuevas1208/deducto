;;;; check.scm --- Natural deduction checker
;;;
;;; The checker evaluates lines in order.  It stops at the first invalid
;;; line and returns a message that names the failed rule or reference.

(define-module (deducto check)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-13)
  #:use-module (ice-9 format)
  #:use-module (deducto formulas)
  #:use-module (deducto proof)
  #:export (check-line
            check-proof
            step-result?
            step-result-number
            step-result-ok?
            step-result-message
            proof-result?
            proof-result-ok?
            proof-result-first-failure
            proof-result-results))

(define-record-type <step-result>
  (make-step-result number ok? message)
  step-result?
  (number step-result-number)
  (ok? step-result-ok?)
  (message step-result-message))

(define-record-type <proof-result>
  (make-proof-result ok? first-failure results)
  proof-result?
  (ok? proof-result-ok?)
  (first-failure proof-result-first-failure)
  (results proof-result-results))

(define (line-at lines number)
  (and (integer? number)
       (positive? number)
       (<= number (length lines))
       (list-ref lines (- number 1))))

(define (min-level-in lines from to)
  (let loop ((number from) (minimum +inf.0))
    (if (> number to)
        minimum
        (loop (+ number 1)
              (min minimum
                   (line-level (list-ref lines (- number 1))))))))

;; A previous line remains available when no later line closes its block.
(define (line-available? lines reference current)
  (let ((target (line-at lines reference)))
    (and target
         (< reference current)
         (>= (min-level-in lines
                           (+ reference 1)
                           (- current 1))
             (line-level target)))))

;; Include the current line when deciding which assumptions remain open.
(define (open-premises-incl lines current)
  (filter (lambda (line)
            (and (eq? (line-rule line) 'premise)
                 (>= (min-level-in lines
                                   (+ (line-number line) 1)
                                   current)
                     (line-level line))))
          (take lines (max 0 (- current 1)))))

(define (open-assumption-vars lines current)
  (fold (lambda (line result)
          (lset-union eq? result (free-vars (line-formula line))))
        '()
        (open-premises-incl lines current)))

(define (span-used-by-line? line span)
  (member span (line-refs line)))

(define (count-span-in-refs references span)
  (length (filter (lambda (reference) (equal? reference span)) references)))

(define (count-span-uses lines current span)
  (let loop ((number 1) (count 0))
    (if (> number current)
        count
        (loop (+ number 1)
              (+ count
                 (count-span-in-refs
                  (line-refs (list-ref lines (- number 1)))
                  span))))))

(define (rule-arity rule)
  (case rule
    ((premise) 0)
    ((repeat or-intro and-elim ex-falso) 1)
    ((and-intro imp-elim not-elim iff-intro iff-elim) 2)
    ((or-elim) 3)
    ((imp-intro not-intro forall-intro) 1)
    ((forall-elim exists-intro exists-elim) 2)
    (else #f)))

;;; Check one line.  IDX is one-based.
(define (check-line lines spans idx)
  (if (or (not (integer? idx))
          (not (positive? idx))
          (> idx (length lines)))
      (make-step-result idx #f "There is no proof line at that position.")
      (let* ((line (list-ref lines (- idx 1)))
             (rule (line-rule line))
             (refs (line-refs line))
             (claimed (line-formula line)))
        (define (fail message)
          (throw 'deducto-step-fail message))

        (define (line-ref position)
          (let ((reference (list-ref refs position)))
            (cond
             ((not (integer? reference))
              (fail (format #f "Reference ~a must be a line number."
                            (+ position 1))))
             ((not (< reference idx))
              (fail (format #f "Line ~a must refer to an earlier line."
                            reference)))
             ((not (line-at lines reference))
              (fail (format #f "There is no line ~a." reference)))
             ((not (line-available? lines reference idx))
              (fail (format #f "Line ~a is inside a closed subproof."
                            reference)))
             (else (line-at lines reference)))))

        (define (span-ref position)
          (let ((reference (list-ref refs position)))
            (cond
             ((not (subproof-span? reference))
              (fail (format #f "Reference ~a must be a subproof span."
                            (+ position 1))))
             ((not (member reference spans))
              (fail (format #f "Subproof (~a . ~a) is not in the proof."
                            (span-start reference)
                            (span-end reference))))
             ((not (< (span-end reference) idx))
              (fail (format #f "Subproof (~a . ~a) is not complete yet."
                            (span-start reference)
                            (span-end reference))))
             ((not (= (count-span-uses lines idx reference) 1))
              (fail (format #f "Subproof (~a . ~a) must be used exactly once."
                            (span-start reference)
                            (span-end reference))))
             (else reference))))

        (define (term-ref position)
          (let ((reference (list-ref refs position)))
            (if (term? reference)
                reference
                (fail "The reference must be a term."))))

        (define (assumption-formula span)
          (let ((first (line-at lines (span-start span))))
            (if (and first (eq? (line-rule first) 'premise))
                (line-formula first)
                (fail (format #f
                              "Subproof (~a . ~a) must start with a premise."
                              (span-start span)
                              (span-end span))))))

        (define (rule-check)
          (case rule
            ((premise)
             (values))
            ((repeat)
             (let ((target (line-ref 0)))
               (if (equal? (line-formula target) claimed)
                   (values)
                   (fail (format #f
                                 "repeat must copy line ~a, which is ~a; found ~a."
                                 (line-number target)
                                 (formula->string (line-formula target))
                                 (formula->string claimed))))))
            ((and-intro)
             (let ((left (line-ref 0))
                   (right (line-ref 1)))
               (if (equal? (list 'and
                                 (line-formula left)
                                 (line-formula right))
                           claimed)
                   (values)
                   (fail (format #f
                                 "and-intro from lines ~a and ~a proves ~a; found ~a."
                                 (line-number left)
                                 (line-number right)
                                 (formula->string
                                  (list 'and
                                        (line-formula left)
                                        (line-formula right)))
                                 (formula->string claimed))))))
            ((and-elim)
             (let* ((source (line-ref 0))
                    (formula (line-formula source)))
               (if (and (pair? formula)
                        (eq? (car formula) 'and)
                        (member claimed (cdr formula)))
                   (values)
                   (fail (format #f
                                 "and-elim on line ~a needs one of its conjuncts; found ~a."
                                 (line-number source)
                                 (formula->string claimed))))))
            ((or-intro)
             (let ((source (line-ref 0)))
               (if (and (pair? claimed)
                        (eq? (car claimed) 'or)
                        (member (line-formula source) (cdr claimed)))
                   (values)
                   (fail (format #f
                                 "or-intro needs line ~a as a disjunct; found ~a."
                                 (line-number source)
                                 (formula->string claimed))))))
            ((imp-elim)
             (let* ((implication (line-ref 0))
                    (antecedent (line-ref 1))
                    (formula (line-formula implication))
                    (given (line-formula antecedent)))
               (if (and (pair? formula)
                        (eq? (car formula) 'if)
                        (equal? (cadr formula) given)
                        (equal? (caddr formula) claimed))
                   (values)
                   (fail (format #f
                                 "imp-elim needs (if A B) and A; lines ~a and ~a do not match."
                                 (line-number implication)
                                 (line-number antecedent))))))
            ((not-elim)
             (let* ((left (line-ref 0))
                    (right (line-ref 1))
                    (left-formula (line-formula left))
                    (right-formula (line-formula right)))
               (if (and (equal? claimed 'false)
                        (or (equal? left-formula (list 'not right-formula))
                            (equal? right-formula (list 'not left-formula))))
                   (values)
                   (fail "not-elim needs A and (not A) to prove false."))))
            ((ex-falso)
             (let ((source (line-ref 0)))
               (if (equal? (line-formula source) 'false)
                   (values)
                   (fail "ex-falso needs a line that proves false."))))
            ((imp-intro)
             (let* ((span (span-ref 0))
                    (assumption (assumption-formula span))
                    (conclusion (line-formula
                                 (line-at lines (span-end span)))))
               (if (equal? claimed (list 'if assumption conclusion))
                   (values)
                   (fail (format #f
                                 "imp-intro must conclude (if ~a ~a)."
                                 (formula->string assumption)
                                 (formula->string conclusion))))))
            ((not-intro)
             (let* ((span (span-ref 0))
                    (assumption (assumption-formula span))
                    (conclusion (line-formula
                                 (line-at lines (span-end span)))))
               (if (and (equal? conclusion 'false)
                        (equal? claimed (list 'not assumption)))
                   (values)
                   (fail (format #f
                                 "not-intro needs a subproof from ~a to false."
                                 (formula->string assumption))))))
            ((iff-intro)
             (let* ((left-span (span-ref 0))
                    (right-span (span-ref 1))
                    (left-assumption (assumption-formula left-span))
                    (left-conclusion (line-formula
                                      (line-at lines (span-end left-span))))
                    (right-assumption (assumption-formula right-span))
                    (right-conclusion (line-formula
                                       (line-at lines (span-end right-span)))))
               (if (and (equal? left-conclusion right-assumption)
                        (equal? right-conclusion left-assumption)
                        (equal? claimed
                               (list 'iff left-assumption left-conclusion)))
                   (values)
                   (fail "iff-intro needs matching proofs in both directions."))))
            ((iff-elim)
             (let* ((source (line-ref 0))
                    (given (line-ref 1))
                    (source-formula (line-formula source))
                    (given-formula (line-formula given)))
               (if (and (pair? source-formula)
                        (eq? (car source-formula) 'iff)
                        (or (and (equal? given-formula (cadr source-formula))
                                 (equal? claimed (caddr source-formula)))
                            (and (equal? given-formula (caddr source-formula))
                                 (equal? claimed (cadr source-formula)))))
                   (values)
                   (fail "iff-elim needs one side of an iff."))))
            ((or-elim)
             (let* ((source (line-ref 0))
                    (left-span (span-ref 1))
                    (right-span (span-ref 2))
                    (source-formula (line-formula source)))
               (if (not (and (pair? source-formula)
                             (eq? (car source-formula) 'or)))
                   (fail "or-elim needs a disjunction as its first reference.")
                   (let* ((left-assumption (assumption-formula left-span))
                          (right-assumption (assumption-formula right-span))
                          (left-conclusion (line-formula
                                            (line-at lines
                                                     (span-end left-span))))
                          (right-conclusion (line-formula
                                             (line-at lines
                                                      (span-end right-span)))))
                     (if (and (equal? left-assumption (cadr source-formula))
                              (equal? right-assumption (caddr source-formula))
                              (equal? left-conclusion right-conclusion)
                              (equal? left-conclusion claimed))
                         (values)
                         (fail "or-elim needs the same conclusion in both cases."))))))
            ((forall-intro)
             (let* ((span (span-ref 0))
                    (assumption (assumption-formula span))
                    (assumption-vars (free-vars assumption))
                    (conclusion (line-formula
                                 (line-at lines (span-end span)))))
               (if (not (= (length assumption-vars) 1))
                   (fail "forall-intro needs one arbitrary variable in its assumption.")
                   (if (not (and (pair? claimed)
                                 (eq? (car claimed) 'forall)))
                       (fail "forall-intro needs a universal conclusion.")
                       (let* ((arbitrary (car assumption-vars))
                              (bound (quantifier-var claimed))
                              (generalized (substitute-free conclusion
                                                             arbitrary
                                                             bound)))
                         (cond
                          ((not generalized)
                           (fail "forall-intro would capture a bound variable."))
                          ((not (equal? (caddr claimed) generalized))
                           (fail "forall-intro must generalize the subproof conclusion."))
                          ((memq arbitrary (open-assumption-vars lines idx))
                           (fail (format #f
                                         "forall-intro needs ~a to be fresh."
                                         arbitrary)))
                          (else (values)))))))
            ((forall-elim)
             (let* ((source (line-ref 0))
                    (term (term-ref 1))
                    (source-formula (line-formula source)))
               (if (not (and (pair? source-formula)
                             (eq? (car source-formula) 'forall)))
                   (fail (format #f
                                 "forall-elim needs a universal formula on line ~a."
                                 (line-number source)))
                   (let ((result (substitute-free
                                  (caddr source-formula)
                                  (quantifier-var source-formula)
                                  term)))
                     (cond
                      ((not result)
                       (fail "forall-elim would capture a bound variable."))
                      ((not (equal? result claimed))
                       (fail "forall-elim does not produce the claimed formula."))
                      (else (values)))))))
            ((exists-intro)
             (let* ((source (line-ref 0))
                    (term (term-ref 1)))
               (if (not (and (pair? claimed)
                             (eq? (car claimed) 'exists)))
                   (fail "exists-intro needs an existential conclusion.")
                   (let ((result (substitute-free
                                  (caddr claimed)
                                  (quantifier-var claimed)
                                  term)))
                     (cond
                      ((not result)
                       (fail "exists-intro would capture a bound variable."))
                      ((not (equal? result (line-formula source)))
                       (fail "exists-intro does not match the source formula."))
                      (else (values)))))))
            ((exists-elim)
             (let* ((source (line-ref 0))
                    (span (span-ref 1))
                    (source-formula (line-formula source))
                    (assumption (assumption-formula span))
                    (conclusion (line-formula
                                 (line-at lines (span-end span))))
                    (assumption-vars (free-vars assumption)))
               (if (not (and (pair? source-formula)
                             (eq? (car source-formula) 'exists)))
                   (fail (format #f
                                 "exists-elim needs an existential formula on line ~a."
                                 (line-number source)))
                   (if (not (= (length assumption-vars) 1))
                       (fail "exists-elim needs one fresh variable in its assumption.")
                       (let* ((witness (quantifier-var source-formula))
                              (arbitrary (car assumption-vars))
                              (needed (substitute-free
                                       (caddr source-formula)
                                       witness
                                       arbitrary)))
                         (cond
                          ((not needed)
                           (fail "exists-elim would capture a bound variable."))
                          ((not (equal? assumption needed))
                           (fail "exists-elim uses the wrong assumption formula."))
                          ((memq arbitrary (open-assumption-vars lines idx))
                           (fail (format #f
                                         "exists-elim needs ~a to be fresh."
                                         arbitrary)))
                          ((memq arbitrary (free-vars conclusion))
                           (fail (format #f
                                         "exists-elim cannot export free variable ~a."
                                         arbitrary)))
                          ((not (equal? conclusion claimed))
                           (fail "exists-elim must conclude the subproof result."))
                          (else (values))))))))
            (else
             (fail (format #f "Unknown rule ~a." rule)))))

        (catch 'deducto-step-fail
          (lambda ()
            (let ((message (formula-error claimed)))
              (when message (fail message)))
            (let ((arity (rule-arity rule)))
              (cond
               ((not arity)
                (fail (format #f "Unknown rule ~a." rule)))
               ((not (= (length refs) arity))
                (fail (format #f
                              "Rule ~a takes ~a reference~a, got ~a."
                              rule
                              arity
                              (if (= arity 1) "" "s")
                              (length refs))))))
            (rule-check)
            (make-step-result idx #t #f))
          (lambda (key message)
            (make-step-result idx #f message)))))))

(define (global-failure lines spans)
  (define number (length lines))
  (define (failure message)
    (make-step-result (+ number 1) #f message))
  (cond
   ((zero? number)
    (failure "The proof is empty."))
   ((find (lambda (span)
            (not (= (count-span-uses lines number span) 1)))
          spans)
    => (lambda (span)
         (if (zero? (count-span-uses lines number span))
             (failure (format #f
                              "Subproof (~a . ~a) is never used."
                              (span-start span)
                              (span-end span)))
             (failure (format #f
                              "Subproof (~a . ~a) must be used exactly once."
                              (span-start span)
                              (span-end span))))))
   ((not (zero? (line-level (line-at lines number))))
    (failure "The proof must end at level 0."))
   ((pair? (free-vars (line-formula (line-at lines number))))
    (failure (format #f
                     "The conclusion has free variables: ~a."
                     (string-join
                      (map symbol->string
                           (free-vars (line-formula (line-at lines number))))
                      " "))))
   (else #f)))

(define (check-proof lines spans)
  (let loop ((number 1) (results '()))
    (if (> number (length lines))
        (let* ((checked (reverse results))
               (invalid (find (lambda (result)
                                (not (step-result-ok? result)))
                              checked))
               (first (or invalid (global-failure lines spans))))
          (if first
              (make-proof-result #f first checked)
              (make-proof-result #t #f checked)))
        (let ((result (check-line lines spans number)))
          (if (step-result-ok? result)
              (loop (+ number 1) (cons result results))
              (make-proof-result #f
                                 result
                                 (reverse (cons result results))))))))