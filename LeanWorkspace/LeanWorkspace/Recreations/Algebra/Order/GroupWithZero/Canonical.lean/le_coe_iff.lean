import Mathlib

variable {α β : Type*}

variable [LE α] {x y : WithZero α} {a b : α}

theorem le_coe_iff : x ≤ b ↔ ∀ a : α, x = ↑a → a ≤ b := WithBot.le_coe_iff

protected lemma _root_.IsMax.withZero (h : IsMax a) : IsMax (a : WithZero α) := h.withBot

