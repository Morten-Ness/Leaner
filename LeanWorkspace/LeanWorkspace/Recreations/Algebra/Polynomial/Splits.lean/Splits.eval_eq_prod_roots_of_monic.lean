import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.eval_eq_prod_roots_of_monic (hf : Polynomial.Splits f) (hm : Monic f) (x : R) :
    f.eval x = (f.roots.map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots, hm]

