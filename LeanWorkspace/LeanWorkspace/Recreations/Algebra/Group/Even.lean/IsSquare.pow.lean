import Mathlib

variable {F α β : Type*}

variable [Monoid α] {n : ℕ} {a : α}

theorem IsSquare.pow (n : ℕ) (ha : IsSquare a) : IsSquare (a ^ n) := by
  aesop (add simp Commute.mul_pow)

