import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

theorem sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
  simpa only [sq] using mul_pos ha ha

