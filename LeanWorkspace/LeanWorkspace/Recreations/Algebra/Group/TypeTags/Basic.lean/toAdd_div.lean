import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.toAdd := rfl

