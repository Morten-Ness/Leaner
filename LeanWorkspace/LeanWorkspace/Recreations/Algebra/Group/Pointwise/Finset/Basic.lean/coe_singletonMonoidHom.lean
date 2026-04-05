import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [MulOneClass α]

theorem coe_singletonMonoidHom : (Finset.singletonMonoidHom : α → Finset α) = singleton := rfl

