import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_C_le : Polynomial.degree (Polynomial.C a) ≤ 0 := by
  by_cases h : a = 0
  · rw [h, C_0]
    exact bot_le
  · rw [Polynomial.degree_C h]

