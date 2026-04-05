import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g := DFunLike.coe_injective h

