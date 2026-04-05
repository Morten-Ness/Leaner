import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftMono M] [MulRightMono M]

theorem lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c := by
  simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)

