import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_ofAdd (x : α) : (Multiplicative.ofAdd x).toAdd = x := rfl

