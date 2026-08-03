(proof
  ((forall (x) (Human x)) premise)
  ((Human Ada) forall-elim 1 Ada)
  ((exists (x) (Human x)) exists-intro 2 Ada))