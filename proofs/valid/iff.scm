(proof
  (Q premise)
  (subproof
    (P premise)
    (Q repeat 1))
  (subproof
    (Q premise)
    (P repeat 1))
  ((iff P Q) iff-intro (2 . 3) (4 . 5)))