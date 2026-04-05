import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_smul_of_isRightRegular_leadingCoeff (ha : a ≠ 0)
    (hp : IsRightRegular p.leadingCoeff) : (a • p).degree = p.degree := by
  refine le_antisymm (Polynomial.degree_smul_le a p) <| degree_le_degree ?_
  rw [coeff_smul, coeff_natDegree, smul_eq_mul, ne_eq]
  exact hp.mul_right_eq_zero_iff.ne.mpr ha

