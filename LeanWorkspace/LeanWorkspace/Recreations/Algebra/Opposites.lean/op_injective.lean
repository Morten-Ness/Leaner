import Mathlib

variable {α β : Type*}

theorem op_injective : Function.Injective (MulOpposite.op : α → αᵐᵒᵖ) := MulOpposite.op_bijective.injective

