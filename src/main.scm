;;;; main.scm --- Deducto command-line interface
;;;
;;; Run with: guile -L src src/main.scm COMMAND ...

(use-modules (srfi srfi-11)
             (ice-9 format)
             (ice-9 match)
             (deducto proof)
             (deducto check)
             (deducto hint)
             (deducto repl))

(define (usage)
  (display
   "Usage:
  deducto check FILE      Check a proof file.
  deducto render FILE     Render a numbered proof.
  deducto hint FILE GOAL  Suggest the next rule.
  deducto repl            Start the proof-building REPL.
")
  (exit 1))

(define (load-proof-file file)
  (call-with-input-file file
    (lambda (port)
      (parse-proof (read port)))))

(define (report-step lines result)
  (let ((number (step-result-number result)))
    (if (<= number (length lines))
        (begin
          (display (line-pretty (list-ref lines (- number 1))))
          (display "  ")
          (if (step-result-ok? result)
              (display "ok")
              (begin
                (display "FAIL: ")
                (display (step-result-message result)))))
        (begin
          (display "[check] ")
          (display (step-result-message result))))
    (newline)))

(define (with-proof-file file action)
  (catch #t
    (lambda ()
      (let-values (((lines spans) (load-proof-file file)))
        (action lines spans)))
    (lambda (key . args)
      (when (eq? key 'quit) (apply throw key args))
      (display "Cannot read that proof: ")
      (display args)
      (newline)
      (exit 2))))

(define (cmd-check file)
  (with-proof-file
   file
   (lambda (lines spans)
     (let ((result (check-proof lines spans)))
       (display (format #f "Deducto: checking ~a~%" file))
       (for-each (lambda (step) (report-step lines step))
                 (proof-result-results result))
       (if (proof-result-ok? result)
           (begin
             (display "Result: valid.")
             (newline)
             (exit 0))
           (begin
             (display "Result: invalid. ")
             (display (step-result-message
                       (proof-result-first-failure result)))
             (newline)
             (exit 1)))))))

(define (cmd-render file)
  (with-proof-file
   file
   (lambda (lines spans)
     (display (render-proof lines))
     (newline)
     (exit 0))))

(define (cmd-hint file goal-text)
  (with-proof-file
   file
   (lambda (lines spans)
     (let ((port (open-input-string goal-text)))
       (let ((goal (read port)))
         (for-each (lambda (suggestion)
                     (display suggestion)
                     (newline))
                   (suggestions-for lines spans goal))))
     (exit 0))))

(define (main arguments)
  (match arguments
    ((_ "check" file) (cmd-check file))
    ((_ "render" file) (cmd-render file))
    ((_ "hint" file goal) (cmd-hint file goal))
    ((_ "repl") (run-repl))
    (_ (usage))))

(main (command-line))