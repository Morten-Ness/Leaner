import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_comp_eq_of_mul_ne_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree ≠ 0) :
    natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases hq : natDegree q = 0
  · exact le_antisymm Polynomial.natDegree_comp_le (by simp [hq])
  apply natDegree_eq_of_le_of_coeff_ne_zero Polynomial.natDegree_comp_le
  rwa [coeff_comp_degree_mul_degree hq]

