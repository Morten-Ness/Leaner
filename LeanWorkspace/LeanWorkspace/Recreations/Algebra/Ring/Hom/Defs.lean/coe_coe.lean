import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F) :
    ((f : α →+* β) : α → β) = f := rfl

attribute [coe] RingHom.toMonoidHom

