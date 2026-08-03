;;;; formulas.scm --- Formula syntax and substitution
;;;
;;; Deducto uses Scheme data as its object language.  Uppercase symbols
;;; name propositions or predicates.  Lowercase symbols name variables.

(define-module (deducto formulas)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-13)
  #:use-module (ice-9 format)
  #:export (term?
            logical-variable?
            predicate-name?
            false?
            formula-error
            valid-formula?
            formula->string
            free-vars
            bound-vars
            substitute-free
            quantifier-var))

(define (lower-case-initial? symbol)
  (let ((name (symbol->string symbol)))
    (and (> (string-length name) 0)
         (char-lower-case? (string-ref name 0)))))

(define (predicate-name? symbol)
  (and (symbol? symbol)
       (let ((name (symbol->string symbol)))
         (and (> (string-length name) 0)
              (char-upper-case? (string-ref name 0))))))

(define (false? formula)
  (eq? formula 'false))

;; Constants and variables are symbols.  The falsum marker is a formula.
(define (term? term)
  (and (symbol? term)
       (not (memq term '(false not and or if iff forall exists)))))

(define (logical-variable? symbol)
  (and (term? symbol)
       (lower-case-initial? symbol)))

(define (binary-connective? symbol)
  (memq symbol '(and or if iff)))

(define (quantifier? symbol)
  (memq symbol '(forall exists)))

(define (union-lists lists)
  (fold (lambda (items result) (lset-union eq? result items)) '() lists))

(define (term-free-vars term)
  (if (logical-variable? term) (list term) '()))

(define (formula-error formula)
  (cond
   ((symbol? formula)
    (if (or (false? formula) (predicate-name? formula))
        #f
        "A formula must use a predicate letter, a predicate, or false."))
   ((not (pair? formula))
    "A formula must be a symbol or a proper list.")
   ((not (list? formula))
    "A formula must be a proper list.")
   ((null? formula)
    "A formula list cannot be empty.")
   (else
    (let ((operator (car formula)))
      (cond
       ((eq? operator 'not)
        (if (= (length formula) 2)
            (formula-error (cadr formula))
            "not takes exactly one formula."))
       ((binary-connective? operator)
        (if (= (length formula) 3)
            (or (formula-error (cadr formula))
                (formula-error (caddr formula)))
            (format #f "~a takes exactly two formulas." operator)))
       ((quantifier? operator)
        (if (= (length formula) 3)
            (let ((variables (cadr formula)))
              (cond
               ((not (and (list? variables)
                          (and-map logical-variable? variables)))
                "Quantifier variables must be variables.")
               ((not (= (length variables) 1))
                "A quantifier binds exactly one variable.")
               (else (formula-error (caddr formula)))))
            "A quantifier takes a variable list and a formula."))
       ((predicate-name? operator)
        (if (and-map term? (cdr formula))
            #f
            "Predicate arguments must be terms."))
       (else
        "Unknown connective or predicate."))))))

(define (valid-formula? formula)
  (not (formula-error formula)))

(define (quantifier-var formula)
  (car (cadr formula)))

(define (formula->string formula)
  (if (formula-error formula)
      (format #f "~s" formula)
      (cond
       ((symbol? formula) (symbol->string formula))
       ((quantifier? (car formula))
        (format #f "(~a (~a) ~a)"
                (car formula)
                (string-join (map symbol->string (cadr formula)) " ")
                (formula->string (caddr formula))))
       (else
        (format #f "(~a ~a)"
                (car formula)
                (string-join (map formula->string (cdr formula)) " "))))))

(define (free-vars formula)
  (cond
   ((symbol? formula)
    (if (logical-variable? formula) (list formula) '()))
   ((quantifier? (car formula))
    (lset-difference eq?
                     (free-vars (caddr formula))
                     (cadr formula)))
   ((memq (car formula) '(not and or if iff))
    (union-lists (map free-vars (cdr formula))))
   (else
    (union-lists (map term-free-vars (cdr formula))))))

(define (bound-vars formula)
  (cond
   ((symbol? formula) '())
   ((quantifier? (car formula))
    (lset-union eq? (cadr formula) (bound-vars (caddr formula))))
   ((memq (car formula) '(not and or if iff))
    (union-lists (map bound-vars (cdr formula))))
   (else '())))

;; Substitute TERM for free occurrences of variable X in FORMULA.
;; Return #f when the substitution would capture a bound variable.
(define (substitute-free formula x term)
  (unless (logical-variable? x)
    (error "substitute-free: the name to replace must be a variable" x))
  (cond
   ((symbol? formula)
    (if (eq? formula x) term formula))
   ((quantifier? (car formula))
    (let ((bound (cadr formula))
          (body (caddr formula)))
      (if (memq x bound)
          formula
          (if (and (memq x (free-vars body))
                   (pair? (lset-intersection eq?
                                              bound
                                              (term-free-vars term))))
              #f
              (let ((result (substitute-free body x term)))
                (and result (list (car formula) bound result)))))))
   ((memq (car formula) '(not and or if iff))
    (let ((result (map (lambda (part) (substitute-free part x term))
                       (cdr formula))))
      (and (not (memq #f result))
           (cons (car formula) result))))
   (else
    (cons (car formula)
          (map (lambda (argument)
                 (if (eq? argument x) term argument))
               (cdr formula))))))