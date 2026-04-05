import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd := rfl

