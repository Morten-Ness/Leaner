import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_degree_of_ne_zero (h : coeff p n ≠ 0) : (n : WithBot ℕ) ≤ Polynomial.degree p := by
  rw [Nat.cast_withBot]
  exact Finset.le_sup (mem_support_iff.2 h)

