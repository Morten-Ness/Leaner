import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem coe_add_eq_bot_iff : a + y = ⊥ ↔ y = ⊥ := by simp

