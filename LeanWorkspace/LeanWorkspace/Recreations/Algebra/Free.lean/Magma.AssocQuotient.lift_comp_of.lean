import Mathlib

variable {α : Type u} [Mul α]

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

theorem lift_comp_of : (Magma.AssocQuotient.lift f).comp Magma.AssocQuotient.of = f := Magma.AssocQuotient.lift.symm_apply_apply f

