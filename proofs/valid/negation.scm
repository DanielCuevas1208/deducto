(proof
  ((not P) premise)
  (subproof
    (P premise)
    (false not-elim 2 1))
  ((not P) not-intro (2 . 3)))