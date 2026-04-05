import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_right_inj [IsRightCancelAdd α] (hz : z ≠ ⊥) : x + z = y + z ↔ x = y := by
  lift z to α using hz; cases x <;> cases y <;> simp [← coe_add]

