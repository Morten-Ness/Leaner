import Mathlib

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

theorem charPoly_monic : LinearRecurrence.charPoly E |>.Monic := by
  nontriviality R
  rw [Polynomial.Monic, leadingCoeff, natDegree_eq_of_degree_eq_some <| LinearRecurrence.charPoly_degree_eq_order _, LinearRecurrence.charPoly,
    coeff_sub, coeff_monomial_same, finset_sum_coeff, sub_eq_self]
  refine sum_eq_zero fun _ _ ↦ coeff_eq_zero_of_degree_lt ?_
  grw [degree_monomial_le]
  simp

