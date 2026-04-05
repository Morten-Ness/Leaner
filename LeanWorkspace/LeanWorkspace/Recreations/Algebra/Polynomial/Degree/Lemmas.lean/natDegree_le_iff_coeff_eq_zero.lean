import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]

