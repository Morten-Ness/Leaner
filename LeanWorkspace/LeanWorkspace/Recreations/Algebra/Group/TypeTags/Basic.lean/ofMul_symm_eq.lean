import Mathlib

variable {α : Type u} {β : Type v}

theorem ofMul_symm_eq : (@Additive.ofMul α).symm = Additive.toMul := rfl

