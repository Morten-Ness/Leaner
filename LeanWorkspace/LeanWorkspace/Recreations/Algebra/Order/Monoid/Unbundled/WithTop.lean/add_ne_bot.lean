import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_ne_bot : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := by cases x <;> cases y <;> simp [← coe_add]

