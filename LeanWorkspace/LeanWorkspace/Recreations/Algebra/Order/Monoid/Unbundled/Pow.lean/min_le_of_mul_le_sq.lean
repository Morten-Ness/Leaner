import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftStrictMono M] [MulRightStrictMono M]

theorem min_le_of_mul_le_sq {a b c : M} (h : a * b ≤ c ^ 2) : min a b ≤ c := by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)

