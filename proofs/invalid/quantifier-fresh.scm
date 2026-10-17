(proof
  ((Context x) premise)
  (subproof
    ((Human x) premise)
    ((Human x) repeat 2))
  ((forall (x) (Human x)) forall-intro (2 . 3)))
