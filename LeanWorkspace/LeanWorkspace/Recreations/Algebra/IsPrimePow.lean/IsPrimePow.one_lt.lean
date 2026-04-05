import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n := h.two_le

