import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_coe_eq_bot_iff : x + b = ⊥ ↔ x = ⊥ := by simp

