import Mathlib

variable {α : Type u} {β : Type v}

theorem toAdd_symm_eq : (@Multiplicative.toAdd α).symm = Multiplicative.ofAdd := rfl

