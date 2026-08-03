;;;; proof.scm --- Proof lines and the nested proof format
;;;
;;; A proof file contains (proof STEP ...).  A step is
;;; (FORMULA RULE REFERENCE ...), or (subproof STEP ...).
;;; Subproof spans use the dotted pair (START . END).

(define-module (deducto proof)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-13)
  #:use-module (ice-9 format)
  #:use-module (deducto formulas)
  #:export (make-line
            line?
            line-number
            line-level
            line-formula
            line-rule
            line-refs
            line-pretty
            parse-proof
            render-line
            render-proof
            proof->spec
            subproof-span?
            span-start
            span-end))

(define-record-type <line>
  (make-line number level formula rule refs)
  line?
  (number line-number)
  (level line-level)
  (formula line-formula)
  (rule line-rule)
  (refs line-refs))

(define (subproof-span? reference)
  (and (pair? reference)
       (integer? (car reference))
       (integer? (cdr reference))
       (positive? (car reference))
       (>= (cdr reference) (car reference))))

(define (span-start span)
  (car span))

(define (span-end span)
  (cdr span))

(define (ref->string reference)
  (if (subproof-span? reference)
      (format #f "(~a . ~a)" (span-start reference) (span-end reference))
      (format #f "~a" reference)))

(define (refs->string references)
  (string-join (map ref->string references) " "))

(define (line-pretty line)
  (format #f "~a~a. ~a"
          (make-string (* 2 (max 0 (line-level line))) #\space)
          (line-number line)
          (formula->string (line-formula line))))

(define (render-line line)
  (let* ((left (line-pretty line))
         (rule (if (pair? (line-refs line))
                   (format #f "~a ~a"
                           (line-rule line)
                           (refs->string (line-refs line)))
                   (format #f "~a" (line-rule line)))))
    (format #f "~a~a~a"
            left
            (make-string (max 1 (- 32 (string-length left))) #\space)
            rule)))

(define (render-proof lines)
  (string-join (map render-line lines) "\n"))

;;; DSL reader ----------------------------------------------------

(define (parse-proof spec)
  (define lines '())
  (define spans '())
  (define next-number 0)

  (define (number!)
    (set! next-number (+ next-number 1))
    next-number)

  (define (check-step-shape step)
    (unless (and (list? step)
                 (>= (length step) 2)
                 (symbol? (cadr step)))
      (error "A proof step must be (FORMULA RULE REF ...):" step)))

  (define (emit-line step level)
    (check-step-shape step)
    (set! lines
          (cons (make-line (number!)
                           level
                           (car step)
                           (cadr step)
                           (cddr step))
                lines)))

  (define (walk steps level)
    (for-each
     (lambda (step)
       (if (and (list? step)
                (pair? step)
                (eq? (car step) 'subproof))
           (let ((inner (cdr step))
                 (start (+ next-number 1)))
             (unless (pair? inner)
               (error "A subproof must contain at least one step:" step))
             (check-step-shape (car inner))
             (unless (eq? (cadr (car inner)) 'premise)
               (error "A subproof must start with a premise:" step))
             (walk inner (+ level 1))
             (set! spans (cons (cons start next-number) spans)))
           (emit-line step level)))
     steps))

  (unless (and (list? spec)
               (pair? spec)
               (eq? (car spec) 'proof))
    (error "A proof must be (proof ...):" spec))
  (walk (cdr spec) 0)
  (values (reverse lines) (reverse spans)))

;;; Round trip back to the DSL ------------------------------------

(define (span-starting-at spans number)
  (find (lambda (span) (= (span-start span) number)) spans))

(define (proof->spec lines spans)
  (define (spec-for from to)
    (let loop ((number from) (items '()))
      (if (> number to)
          (reverse items)
          (let ((span (span-starting-at spans number)))
            (if span
                (loop (+ (span-end span) 1)
                      (cons (cons 'subproof
                                  (spec-for number (span-end span)))
                            items))
                (let ((line (list-ref lines (- number 1))))
                  (loop (+ number 1)
                        (cons (append (list (line-formula line)
                                            (line-rule line))
                                      (line-refs line))
                              items))))))))
  (cons 'proof (spec-for 1 (length lines))))