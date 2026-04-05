import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem ofRingHom_coe_ringHom (f : R ≃+* S) (g : S →+* R) (h₁ h₂) : RingEquiv.ofRingHom (↑f) g h₁ h₂ = f := RingEquiv.ext fun _ ↦ rfl

