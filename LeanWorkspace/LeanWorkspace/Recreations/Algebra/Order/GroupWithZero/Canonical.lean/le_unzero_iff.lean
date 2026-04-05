import Mathlib

variable {α β : Type*}

variable [LE α] {x y : WithZero α} {a b : α}

theorem le_unzero_iff (hy : y ≠ 0) : a ≤ unzero hy ↔ a ≤ y := WithBot.le_unbot_iff _

