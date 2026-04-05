import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_neg [Neg α] (x : α) : Multiplicative.ofAdd (-x) = (Multiplicative.ofAdd x)⁻¹ := rfl

