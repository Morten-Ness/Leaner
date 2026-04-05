import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.eq_prod_roots_of_monic (hf : Polynomial.Splits f) (hm : f.Monic) :
    f = (f.roots.map (X - C ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots, hm.leadingCoeff, C_1, one_mul]

