import Mathlib

variable {F α β γ : Type*}

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

theorem coe_mulHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ := rfl

