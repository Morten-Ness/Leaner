import Mathlib

variable {F ι κ G M N O : Type*}

variable [AddCommMonoid M]

theorem coe_sumAddMonoidHom : (Multiset.sumAddMonoidHom : Multiset M → M) = sum := rfl

