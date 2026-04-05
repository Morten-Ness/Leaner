import Mathlib

variable {α β : Type*}

variable [LT α] {x y : WithZero α} {a b : α}

theorem lt_def : x < y ↔ x = 0 ∧ (∃ b : α, y = b) ∨ ∃ a b : α, a < b ∧ x = ↑a ∧ y = ↑b := WithBot.lt_def

