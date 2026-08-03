;;;; repl.scm --- Interactive proof construction
;;;
;;; The REPL keeps a flat line list and creates subproof spans when a
;;; subproof closes.  It checks each new line before adding it.

(define-module (deducto repl)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-11)
  #:use-module (ice-9 format)
  #:use-module (deducto formulas)
  #:use-module (deducto proof)
  #:use-module (deducto check)
  #:use-module (deducto hint)
  #:export (run-repl))

(define (subproof-arity rule)
  (case rule
    ((imp-intro not-intro forall-intro exists-elim) 1)
    ((or-elim iff-intro) 2)
    (else #f)))

(define (path-string value)
  (cond
   ((string? value) value)
   ((symbol? value) (symbol->string value))
   (else #f)))

(define* (run-repl #:optional (input-port (current-input-port))
                              (output-port (current-output-port)))
  (define lines '())
  (define spans '())
  (define level 0)
  (define open-stack '())
  (define goal #f)

  (define (say . values)
    (for-each (lambda (value) (display value output-port)) values)
    (newline output-port))

  (define (next-line-number)
    (+ (length lines) 1))

  (define (commit! candidate-lines candidate-spans)
    (let ((result (check-line candidate-lines
                              candidate-spans
                              (length candidate-lines))))
      (if (step-result-ok? result)
          (begin
            (set! lines candidate-lines)
            (set! spans candidate-spans)
            #t)
          (begin
            (say (step-result-message result))
            #f))))

  (define (add-premise formula)
    (if (> level 0)
        (say "Use (open F) for a subproof assumption.")
        (let ((line (make-line (next-line-number) 0 formula 'premise '())))
          (when (commit! (append lines (list line)) spans)
            (say "Premise added: " (line-pretty line))))))

  (define (open-subproof formula)
    (let* ((line (make-line (next-line-number)
                            (+ level 1)
                            formula
                            'premise
                            '()))
           (candidate (append lines (list line))))
      (when (commit! candidate spans)
        (set! open-stack (cons (line-number line) open-stack))
        (set! level (+ level 1))
        (say "Assumption added: " (line-pretty line)))))

  (define (built-spans arity)
    (cond
     ((= arity 1)
      (list (cons (car open-stack) (length lines))))
     ((= arity 2)
      (list (cons (list-ref open-stack 1)
                  (- (car open-stack) 1))
            (cons (car open-stack) (length lines))))
     (else '())))

  (define (close-subproof rule formula references)
    (let ((arity (subproof-arity rule)))
      (cond
       ((not arity)
        (say (format #f
                     "~a does not close a subproof. Use (step ...)."
                     rule)))
       ((< (length open-stack) arity)
        (say "Not enough open subproofs for that rule."))
       (else
        (let* ((new-spans (built-spans arity))
               (all-references (append references new-spans))
               (line (make-line (next-line-number)
                                (- level arity)
                                formula
                                rule
                                all-references))
               (candidate-lines (append lines (list line)))
               (candidate-spans (append spans new-spans)))
          (when (commit! candidate-lines candidate-spans)
            (set! open-stack (list-tail open-stack arity))
            (set! level (- level arity))
            (say "Line added: " (line-pretty line))))))))

  (define (add-step rule formula references)
    (if (subproof-arity rule)
        (say (format #f
                     "~a closes a subproof. Use (close ~a ...)."
                     rule
                     rule))
        (let ((line (make-line (next-line-number)
                               level
                               formula
                               rule
                               references)))
          (when (commit! (append lines (list line)) spans)
            (say "Line added: " (line-pretty line))))))

  (define (show-check)
    (let ((result (check-proof lines spans)))
      (for-each
       (lambda (step)
         (let ((number (step-result-number step)))
           (if (<= number (length lines))
               (say (line-pretty (list-ref lines (- number 1)))
                    "  "
                    (if (step-result-ok? step) "ok" "FAIL"))
               (say (format #f "[check] ~a"
                             (step-result-message step))))))
       (proof-result-results result))
      (if (proof-result-ok? result)
          (say "Result: valid.")
          (say "Result: invalid. "
               (step-result-message
                (proof-result-first-failure result))))))

  (define (show-proof)
    (if (null? lines)
        (say "The proof is empty.")
        (say (render-proof lines))))

  (define (show-status)
    (say (format #f
                 "Lines: ~a  Level: ~a  Open subproofs: ~a"
                 (length lines)
                 level
                 (length open-stack)))
    (when goal
      (say "Goal: " (formula->string goal))))

  (define (show-hint formula)
    (let ((target (or formula goal)))
      (cond
       ((not target)
        (say "Set a goal with (goal F) or pass F to (hint F)."))
       ((formula-error target)
        (say (formula-error target)))
       (else
        (for-each (lambda (suggestion) (say "* " suggestion))
                  (suggestions-for lines spans target))))))

  (define (set-goal formula)
    (if (formula-error formula)
        (say (formula-error formula))
        (begin
          (set! goal formula)
          (say "Goal set: " (formula->string formula)))))

  (define (save-proof value)
    (let ((file (path-string value)))
      (cond
       ((not file) (say "Save needs a file name string."))
       ((> level 0) (say "Close all subproofs before saving."))
       (else
        (catch #t
          (lambda ()
            (call-with-output-file file
              (lambda (port)
                (write (proof->spec lines spans) port)
                (newline port)))
            (say (format #f "Saved ~a lines to ~a." (length lines) file)))
          (lambda (key . args)
            (say (format #f "Cannot save that proof: ~a" args))))))))

  (define (load-proof value)
    (let ((file (path-string value)))
      (if (not file)
          (say "Load needs a file name string.")
          (catch #t
            (lambda ()
              (let-values (((candidate-lines candidate-spans)
                            (call-with-input-file file
                              (lambda (port)
                                (parse-proof (read port))))))
                (let ((result (check-proof candidate-lines candidate-spans)))
                  (if (proof-result-ok? result)
                      (begin
                        (set! lines candidate-lines)
                        (set! spans candidate-spans)
                        (set! level 0)
                        (set! open-stack '())
                        (set! goal #f)
                        (say (format #f
                                     "Loaded a valid proof with ~a lines."
                                     (length candidate-lines))))
                      (say "Cannot load an invalid proof: "
                           (step-result-message
                            (proof-result-first-failure result)))))))
            (lambda (key . args)
              (say (format #f "Cannot load that proof: ~a" args)))))))

  (define (help)
    (say
     "(premise F)          Add a top-level premise."
     "(open F)             Start a subproof with assumption F."
     "(step RULE F REF...) Add a checked line."
     "(close RULE F REF...) Close open subproofs."
     "(goal F)             Set the hint goal."
     "(hint F)             Suggest the next rule."
     "(check)              Check the complete proof."
     "(show)               Render the proof."
     "(status)             Show the current state."
     "(save FILE)          Save the proof."
     "(load FILE)          Load a valid proof."
     "(quit)               Exit the REPL."))

  (define (prompt)
    (if (zero? level)
        "deducto> "
        (format #f "deducto[~a]> " level)))

  (define (dispatch expression)
    (case (car expression)
      ((premise)
       (if (= (length expression) 2)
           (add-premise (cadr expression))
           (help)))
      ((open assume)
       (if (= (length expression) 2)
           (open-subproof (cadr expression))
           (help)))
      ((close)
       (if (>= (length expression) 3)
           (close-subproof (cadr expression)
                           (caddr expression)
                           (cdddr expression))
           (help)))
      ((step)
       (if (>= (length expression) 3)
           (add-step (cadr expression)
                     (caddr expression)
                     (cdddr expression))
           (help)))
      ((goal)
       (if (= (length expression) 2)
           (set-goal (cadr expression))
           (help)))
      ((hint)
       (show-hint (if (= (length expression) 2)
                      (cadr expression)
                      #f)))
      ((check) (show-check))
      ((show) (show-proof))
      ((status) (show-status))
      ((save)
       (if (= (length expression) 2)
           (save-proof (cadr expression))
           (help)))
      ((load)
       (if (= (length expression) 2)
           (load-proof (cadr expression))
           (help)))
      ((help) (help))
      ((quit) (values))
      (else
       (say "Unknown command.")
       (help))))

  (let loop ()
    (display (prompt) output-port)
    (flush-output-port output-port)
    (let ((expression (read input-port)))
      (cond
       ((eof-object? expression)
        (newline output-port))
       ((not (and (pair? expression) (list? expression)))
        (say "Commands are proper s-expressions. Type (help).")
        (loop))
       (else
        (dispatch expression)
        (unless (eq? (car expression) 'quit)
          (loop))))))
  (values lines spans level))