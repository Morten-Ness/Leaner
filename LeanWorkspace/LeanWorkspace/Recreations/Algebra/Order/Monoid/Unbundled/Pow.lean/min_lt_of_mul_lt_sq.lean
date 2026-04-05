import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftMono M] [MulRightMono M]

theorem min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c := by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)

