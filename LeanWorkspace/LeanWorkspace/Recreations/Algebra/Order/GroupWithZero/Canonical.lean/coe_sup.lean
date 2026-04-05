import Mathlib

variable {α β : Type*}

theorem coe_sup [SemilatticeSup α] (a b : α) : ((a ⊔ b : α) : WithZero α) = (a : WithZero α) ⊔ b := rfl

