import Mathlib

variable {α β : Type*}

variable [LE α] {x y : WithZero α} {a b : α}

theorem not_coe_le_zero (a : α) : ¬(a : WithZero α) ≤ 0 := WithBot.not_coe_le_bot _

