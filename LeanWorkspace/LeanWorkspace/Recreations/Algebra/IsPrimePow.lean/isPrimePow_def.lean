import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem isPrimePow_def : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n := Iff.rfl

