(proof
  (P premise)
  ((exists (x) (Human x)) premise)
  (subproof
    ((Human x) premise)
    (P repeat 1))
  (P exists-elim 2 (3 . 4)))