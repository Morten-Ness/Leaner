import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]} {a : R}

variable [NoZeroDivisors R]

theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    · simp only [Ne, mul_eq_zero, leadingCoeff_eq_zero, p0, Polynomial.natDegree_comp_eq_of_mul_ne_zero,
        ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero q0), not_false_eq_true, pow_ne_zero, or_self]

