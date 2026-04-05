import Mathlib

variable {α : Type u} {β : Type v} [Mul β] (f : α → β)

theorem lift_comp_of' (f : FreeMagma α →ₙ* β) : FreeMagma.lift (f ∘ of) = f := FreeMagma.lift.apply_symm_apply f

