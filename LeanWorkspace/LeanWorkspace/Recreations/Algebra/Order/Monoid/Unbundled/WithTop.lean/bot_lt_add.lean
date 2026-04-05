import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem bot_lt_add [LT α] : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp_rw [WithBot.bot_lt_iff_ne_bot, WithBot.add_ne_bot]

