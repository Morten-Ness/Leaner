import Mathlib

variable {α β : Type*}

theorem op_smul [SMul α β] (a : α) (b : β) : MulOpposite.op (a • b) = a • MulOpposite.op b := rfl

