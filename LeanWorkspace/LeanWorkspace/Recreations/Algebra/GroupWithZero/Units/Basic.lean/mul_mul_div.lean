import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) := (hb.isUnit.mul_mul_div _).symm

