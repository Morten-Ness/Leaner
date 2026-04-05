import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem coe_ringHom_ofRingHom (f : R →+* S) (g : S →+* R) (h₁ h₂) : RingEquiv.ofRingHom f g h₁ h₂ = f := rfl

