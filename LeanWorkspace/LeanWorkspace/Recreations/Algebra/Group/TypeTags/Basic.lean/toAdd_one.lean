import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0 := rfl

