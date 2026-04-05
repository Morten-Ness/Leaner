import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem coe_monoidHom_injective : Function.Injective (fun f : α →+* β => (f : α →* β)) := Function.Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

