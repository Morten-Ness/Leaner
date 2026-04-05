import Mathlib

variable {α β : Type*}

theorem op_bijective : Function.Bijective (MulOpposite.op : α → αᵐᵒᵖ) := MulOpposite.opEquiv.bijective

