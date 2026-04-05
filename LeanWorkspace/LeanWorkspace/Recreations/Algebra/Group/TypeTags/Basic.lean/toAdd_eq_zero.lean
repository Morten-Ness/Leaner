import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_eq_zero {α : Type*} [Zero α] {x : Multiplicative α} :
    x.toAdd = 0 ↔ x = 1 := Iff.rfl

