import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t =>
  not_isPrimePow_one (t ▸ h)

