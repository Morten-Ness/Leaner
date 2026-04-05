import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [DivisionCommMonoid α]

theorem invMonoidHom_apply (a : α) : invMonoidHom a = a⁻¹ := rfl

