import Mathlib

variable {α β : Type*}

variable [LT α] {x y : WithZero α} {a b : α}

theorem unzero_lt_iff (hx : x ≠ 0) : unzero hx < b ↔ x < b := WithBot.unbot_lt_iff _

