import Mathlib

variable {F α β γ : Type*}

variable [MulOneClass α]

theorem coe_singletonMonoidHom : (Set.singletonMonoidHom : α → Set α) = singleton := rfl

