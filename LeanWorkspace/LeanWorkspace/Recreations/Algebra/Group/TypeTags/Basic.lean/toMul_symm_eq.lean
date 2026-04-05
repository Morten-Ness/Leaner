import Mathlib

variable {α : Type u} {β : Type v}

theorem toMul_symm_eq : (@Additive.toMul α).symm = Additive.ofMul := rfl

