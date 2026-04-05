import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem coe_singletonOneHom : (Finset.singletonOneHom : α → Finset α) = singleton := rfl

