import Mathlib

variable {α β : Type*}

variable [LE α] {x y : WithZero α} {a b : α}

theorem le_def : x ≤ y ↔ ∀ a : α, x = ↑a → ∃ b : α, y = ↑b ∧ a ≤ b := WithBot.le_iff_forall

