import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

theorem eval_rootOfSplits (hf : f.Splits) (hfd : f.degree ≠ 0) :
    f.eval (Polynomial.rootOfSplits hf hfd) = 0 := Classical.choose_spec <| hf.exists_eval_eq_zero hfd

