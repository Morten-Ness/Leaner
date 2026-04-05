import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem symm_ofNonUnitalRingHom (f : R →ₙ+* S) (g : S →ₙ+* R) (h₁ h₂) :
    (RingEquiv.ofNonUnitalRingHom f g h₁ h₂).symm = RingEquiv.ofNonUnitalRingHom g f h₂ h₁ := rfl

