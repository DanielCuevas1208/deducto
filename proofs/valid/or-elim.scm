(proof
  ((or P Q) premise)
  (R premise)
  (subproof
    (P premise)
    (R repeat 2))
  (subproof
    (Q premise)
    (R repeat 2))
  (R or-elim 1 (3 . 4) (5 . 6)))