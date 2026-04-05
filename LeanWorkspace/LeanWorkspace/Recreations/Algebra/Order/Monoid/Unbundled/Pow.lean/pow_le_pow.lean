import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

theorem pow_le_pow {a b : M} (hab : a ≤ b) (ht : 1 ≤ b) {m n : ℕ} (hmn : m ≤ n) : a ^ m ≤ b ^ n := (pow_le_pow_left' hab _).trans (pow_le_pow_right' ht hmn)

