import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.eval_root_derivative [DecidableEq R] (hf : f.Splits) (hm : f.Monic) {x : R}
    (hx : x ∈ f.roots) : eval x f.derivative = ((f.roots.erase x).map (x - ·)).prod := by
  rw [← eval_multiset_prod_X_sub_C_derivative hx, ← hf.eq_prod_roots_of_monic hm]

