import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_symm_eq : (@Multiplicative.ofAdd α).symm = Multiplicative.toAdd := rfl

