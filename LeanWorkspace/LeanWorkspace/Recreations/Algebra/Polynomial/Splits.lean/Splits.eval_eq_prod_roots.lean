import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.eval_eq_prod_roots (hf : Polynomial.Splits f) (x : R) :
    f.eval x = f.leadingCoeff * (f.roots.map (x - ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval_multiset_prod]

