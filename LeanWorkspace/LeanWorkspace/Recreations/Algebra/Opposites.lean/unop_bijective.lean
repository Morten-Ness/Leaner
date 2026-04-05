import Mathlib

variable {α β : Type*}

theorem unop_bijective : Function.Bijective (MulOpposite.unop : αᵐᵒᵖ → α) := MulOpposite.opEquiv.symm.bijective

