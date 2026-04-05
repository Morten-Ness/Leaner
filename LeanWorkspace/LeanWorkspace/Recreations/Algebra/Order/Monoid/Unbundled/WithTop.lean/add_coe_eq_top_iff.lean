import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem add_coe_eq_top_iff : x + b = ⊤ ↔ x = ⊤ := by simp

