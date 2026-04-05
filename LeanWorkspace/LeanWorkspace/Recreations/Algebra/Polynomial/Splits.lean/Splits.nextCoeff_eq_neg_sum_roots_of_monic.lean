import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.nextCoeff_eq_neg_sum_roots_of_monic (hf : Polynomial.Splits f) (hm : Monic f) :
    f.nextCoeff = -f.roots.sum := by
  simp [hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hm]

