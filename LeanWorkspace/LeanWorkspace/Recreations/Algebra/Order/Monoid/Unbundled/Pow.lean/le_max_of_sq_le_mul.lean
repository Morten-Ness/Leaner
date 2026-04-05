import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftStrictMono M] [MulRightStrictMono M]

theorem le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 ≤ b * c) : a ≤ max b c := by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

