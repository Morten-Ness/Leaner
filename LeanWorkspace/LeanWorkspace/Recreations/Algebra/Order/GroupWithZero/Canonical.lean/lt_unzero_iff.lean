import Mathlib

variable {α β : Type*}

variable [LT α] {x y : WithZero α} {a b : α}

theorem lt_unzero_iff (hy : y ≠ 0) : a < unzero hy ↔ a < y := WithBot.lt_unbot_iff _

