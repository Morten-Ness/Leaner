import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.coeff_zero_eq_prod_roots_of_monic (hf : Polynomial.Splits f) (hm : Monic f) :
    coeff f 0 = (-1) ^ f.natDegree * f.roots.prod := by
  simp [hf.coeff_zero_eq_leadingCoeff_mul_prod_roots, hm]

