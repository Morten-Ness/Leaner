import Mathlib

variable {α β : Type*}

variable [LE α] {x y : WithZero α} {a b : α}

theorem unbot_le_iff (hx : x ≠ 0) : unzero hx ≤ b ↔ x ≤ b := WithBot.unbot_le_iff _

