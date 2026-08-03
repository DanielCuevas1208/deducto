(proof
  ((Context x) premise)
  (subproof
    ((Human x) premise)
    (P repeat 1))
  ((forall (x) P) forall-intro (2 . 3)))