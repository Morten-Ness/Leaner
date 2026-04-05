import Mathlib

variable {α β : Type*}

variable [LT α] {x y : WithZero α} {a b : α}

theorem lt_iff_exists_coe : x < y ↔ ∃ b : α, y = b ∧ x < b := WithBot.lt_iff_exists_coe

