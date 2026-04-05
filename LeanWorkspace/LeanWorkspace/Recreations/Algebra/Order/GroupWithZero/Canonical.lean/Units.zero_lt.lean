import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem Units.zero_lt (u : αˣ) : (0 : α) < u := zero_lt_iff.2 u.ne_zero

