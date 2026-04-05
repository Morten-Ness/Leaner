import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff (hf : Polynomial.Splits f) :
    f.nextCoeff = -f.leadingCoeff * f.roots.sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

