import Mathlib

variable {F α β γ : Type*}

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

theorem coe_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α → β) = f := rfl

