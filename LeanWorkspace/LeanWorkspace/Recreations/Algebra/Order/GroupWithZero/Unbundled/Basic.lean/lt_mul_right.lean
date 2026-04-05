import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

theorem lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

