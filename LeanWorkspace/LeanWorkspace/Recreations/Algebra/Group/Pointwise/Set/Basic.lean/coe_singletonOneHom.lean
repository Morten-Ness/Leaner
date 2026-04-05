import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem coe_singletonOneHom : (Set.singletonOneHom : α → Set α) = singleton := rfl

