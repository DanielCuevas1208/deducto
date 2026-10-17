(proof
  ((if P Q) premise)
  ((if Q P) premise)
  (subproof
    (P premise)
    (Q imp-elim 1 3))
  (subproof
    (Q premise)
    (P imp-elim 2 5))
  ((iff P Q) iff-intro (3 . 4) (5 . 6)))
