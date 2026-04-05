import Mathlib

variable {α β : Type*}

theorem unop_injective : Function.Injective (MulOpposite.unop : αᵐᵒᵖ → α) := MulOpposite.unop_bijective.injective

