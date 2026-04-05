import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

theorem mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f := RingHom.ext fun _ => rfl

