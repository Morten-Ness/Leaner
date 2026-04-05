import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots (hf : Polynomial.Splits f) :
    f.coeff 0 = (-1) ^ f.natDegree * f.leadingCoeff * f.roots.prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [coeff_zero_eq_eval_zero, eval_multiset_prod, hf.natDegree_eq_card_roots,
    mul_assoc, mul_left_comm]

