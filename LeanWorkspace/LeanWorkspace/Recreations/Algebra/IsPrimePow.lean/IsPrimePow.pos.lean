import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n := pos_of_gt hn.two_le

