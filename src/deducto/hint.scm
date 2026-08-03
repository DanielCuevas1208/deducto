;;;; hint.scm --- Rule suggestions for the next proof step
;;;
;;; Hints are heuristic.  They inspect the goal and formulas already
;;; available in the proof.  They never change the proof.

(define-module (deducto hint)
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 format)
  #:use-module (deducto formulas)
  #:use-module (deducto proof)
  #:export (suggestions-for
            hint-for
            fresh-variable))

(define (union-lists lists)
  (fold (lambda (items result) (lset-union eq? result items)) '() lists))

(define (available-formulas lines)
  (map (lambda (line)
         (list (line-number line) (line-formula line)))
       lines))

(define (variables-in formula)
  (cond
   ((symbol? formula)
    (if (logical-variable? formula) (list formula) '()))
   ((memq (car formula) '(forall exists))
    (lset-union eq?
                (cadr formula)
                (variables-in (caddr formula))))
   (else
    (union-lists (map variables-in (cdr formula))))))

(define (terms-in formula)
  (cond
   ((symbol? formula) '())
   ((memq (car formula) '(forall exists))
    (terms-in (caddr formula)))
   ((memq (car formula) '(not and or if iff))
    (union-lists (map terms-in (cdr formula))))
   ((predicate-name? (car formula))
    (lset-union eq? (cdr formula) '()))
   (else '())))

(define (fresh-variable lines)
  (let ((used (union-lists
               (map variables-in (map line-formula lines)))))
    (let loop ((number 0))
      (let ((candidate (string->symbol
                        (string-append "x" (number->string number)))))
        (if (memq candidate used)
            (loop (+ number 1))
            candidate)))))

(define (find-line-with lines formula)
  (find (lambda (entry) (equal? (cadr entry) formula))
        (available-formulas lines)))

(define (find-witness lines goal)
  (let* ((variable (quantifier-var goal))
         (body (caddr goal))
         (terms (union-lists
                 (map terms-in (map line-formula lines)))))
    (find (lambda (term)
            (let ((instance (substitute-free body variable term)))
              (and instance (find-line-with lines instance) #t)))
          terms)))

(define (suggestions-for lines spans goal)
  (if (formula-error goal)
      (list (formula-error goal))
      (let ((have (find-line-with lines goal)))
        (cond
         (have
          (list (format #f "Line ~a already proves the goal." (car have))))
         ((and (pair? goal) (eq? (car goal) 'if))
          (list (format #f
                        "Use imp-intro. Assume ~a and derive ~a."
                        (formula->string (cadr goal))
                        (formula->string (caddr goal)))))
         ((and (pair? goal) (eq? (car goal) 'and))
          (list (format #f
                        "Use and-intro. Derive ~a and ~a."
                        (formula->string (cadr goal))
                        (formula->string (caddr goal)))))
         ((and (pair? goal) (eq? (car goal) 'or))
          (list (format #f
                        "Use or-intro. Derive one disjunct."
                        )))
         ((and (pair? goal) (eq? (car goal) 'not))
          (list (format #f
                        "Use not-intro. Assume ~a and derive false."
                        (formula->string (cadr goal)))))
         ((and (pair? goal) (eq? (car goal) 'iff))
          (list "Use iff-intro. Prove both directions."))
         ((and (pair? goal) (eq? (car goal) 'forall))
          (let* ((variable (quantifier-var goal))
                 (fresh (fresh-variable lines))
                 (assumption (substitute-free (caddr goal)
                                              variable
                                              fresh)))
            (list (format #f
                          "Use forall-intro. Assume ~a with fresh ~a."
                          (formula->string assumption)
                          fresh))))
         ((and (pair? goal) (eq? (car goal) 'exists))
          (let ((witness (find-witness lines goal)))
            (list (if witness
                      (format #f
                              "Use exists-intro with witness ~a."
                              witness)
                      "Use exists-intro. Choose a suitable constant."))))
         (else
          (let ((implication
                 (find (lambda (entry)
                         (let ((formula (cadr entry)))
                           (and (pair? formula)
                                (eq? (car formula) 'if)
                                (equal? (caddr formula) goal)
                                (find-line-with lines (cadr formula)))))
                       (available-formulas lines)))
            (cond
             (implication
              (let ((antecedent
                     (find-line-with lines
                                     (cadr (cadr implication)))))
                (list (format #f
                              "Use imp-elim with lines ~a and ~a."
                              (car implication)
                              (car antecedent)))))
             ((find (lambda (entry)
                      (let ((formula (cadr entry)))
                        (and (pair? formula)
                             (eq? (car formula) 'or))))
                    (available-formulas lines))
              => (lambda (entry)
                   (list (format #f
                                 "Use or-elim on line ~a."
                                 (car entry)))))
             ((find (lambda (entry)
                      (let ((formula (cadr entry)))
                        (and (pair? formula)
                             (eq? (car formula) 'not)
                             (equal? (cadr formula) goal))))
                    (available-formulas lines))
              => (lambda (entry)
                   (list (format #f
                                 "Use not-elim with line ~a."
                                 (car entry)))))
             ((find (lambda (entry)
                      (let ((formula (cadr entry)))
                        (and (pair? formula)
                             (eq? (car formula) 'iff)
                             (or (equal? (cadr formula) goal)
                                 (equal? (caddr formula) goal)))))
                    (available-formulas lines))
              => (lambda (entry)
                   (list (format #f
                                 "Use iff-elim on line ~a."
                                 (car entry)))))
             ((find (lambda (entry)
                      (let ((formula (cadr entry)))
                        (and (pair? formula)
                             (eq? (car formula) 'forall)
                             (find (lambda (term)
                                     (let ((instance
                                            (substitute-free
                                             (caddr formula)
                                             (quantifier-var formula)
                                             term)))
                                       (and instance
                                            (equal? instance goal))))
                                   (union-lists
                                    (map terms-in
                                         (map line-formula lines)))))))
                    (available-formulas lines))
              => (lambda (entry)
                   (list (format #f
                                 "Use forall-elim on line ~a."
                                 (car entry)))))
             (else
              (list (format #f
                            "No obvious step. Try assuming (not ~a)."
                            (formula->string goal))))))))))))

(define (hint-for lines spans goal)
  (let ((suggestions (suggestions-for lines spans goal)))
    (if (pair? suggestions)
        (car suggestions)
        "No hint available.")))