import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.eval_derivative [DecidableEq R] (hf : f.Splits) (x : R) :
    eval x f.derivative = f.leadingCoeff *
      (f.roots.map fun a ↦ ((f.roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

