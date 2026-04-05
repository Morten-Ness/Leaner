import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem card_support_C_mul_X_pow_le_one {c : R} {n : ℕ} : #(support (Polynomial.C c * Polynomial.X ^ n)) ≤ 1 := by
  rw [← card_singleton n]
  apply card_le_card (support_C_mul_X_pow' n c)

