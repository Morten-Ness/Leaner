import Mathlib

variable {α β : Type*}

theorem unop_smul [SMul α β] (a : α) (b : βᵐᵒᵖ) : MulOpposite.unop (a • b) = a • MulOpposite.unop b := rfl

