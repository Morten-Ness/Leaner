import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_left_inj [IsLeftCancelAdd α] (hx : x ≠ ⊥) : x + y = x + z ↔ y = z := by
  lift x to α using hx; cases y <;> cases z <;> simp [← coe_add]

