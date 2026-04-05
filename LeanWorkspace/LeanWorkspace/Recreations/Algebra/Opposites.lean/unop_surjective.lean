import Mathlib

variable {α β : Type*}

theorem unop_surjective : Function.Surjective (MulOpposite.unop : αᵐᵒᵖ → α) := MulOpposite.unop_bijective.surjective

