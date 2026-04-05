import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem ofRingHom_symm (f : R →+* S) (g : S →+* R) (h₁ h₂) :
    (RingEquiv.ofRingHom f g h₁ h₂).symm = RingEquiv.ofRingHom g f h₂ h₁ := rfl

