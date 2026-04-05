import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [DivisionCommMonoid α]

theorem coe_invMonoidHom : (invMonoidHom : α → α) = Inv.inv := rfl

