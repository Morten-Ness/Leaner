import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem coeMonoidHom_apply (s : Finset α) : Finset.coeMonoidHom s = s := rfl

