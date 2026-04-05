import Mathlib

variable {α β : Type*}

variable [LT α] {x y : WithZero α} {a b : α}

theorem lt_coe_iff : x < b ↔ ∀ a : α, x = a → a < b := WithBot.lt_coe_iff

