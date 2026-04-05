import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p := ⟨p, 1, hp, zero_lt_one, by simp⟩

