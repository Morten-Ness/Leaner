import Mathlib

variable {α β : Type*}

variable [LT α] {x y : WithZero α} {a b : α}

theorem lt_iff_exists : x < y ↔ ∃ b : α, y = ↑b ∧ ∀ a : α, x = ↑a → a < b := WithBot.lt_iff_exists

