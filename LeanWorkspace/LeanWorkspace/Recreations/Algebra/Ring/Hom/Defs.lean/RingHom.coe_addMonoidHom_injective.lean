import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem coe_addMonoidHom_injective : Function.Injective (fun f : α →+* β => (f : α →+ β)) := fun _ _ h =>
  RingHom.ext <| DFunLike.congr_fun (F := α →+ β) h

