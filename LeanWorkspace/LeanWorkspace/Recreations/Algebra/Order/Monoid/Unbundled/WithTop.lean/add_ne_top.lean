import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem add_ne_top : x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by cases x <;> cases y <;> simp [← coe_add]

