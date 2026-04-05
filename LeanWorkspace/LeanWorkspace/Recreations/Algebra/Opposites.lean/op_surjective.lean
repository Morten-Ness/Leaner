import Mathlib

variable {α β : Type*}

theorem op_surjective : Function.Surjective (MulOpposite.op : α → αᵐᵒᵖ) := MulOpposite.op_bijective.surjective

