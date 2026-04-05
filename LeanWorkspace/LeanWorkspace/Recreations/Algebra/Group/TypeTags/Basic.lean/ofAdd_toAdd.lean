import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_toAdd (x : Multiplicative α) : Multiplicative.ofAdd x.toAdd = x := rfl

