import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem coe_monoidHom_refl : (RingEquiv.refl R : R →* R) = MonoidHom.id R := rfl

