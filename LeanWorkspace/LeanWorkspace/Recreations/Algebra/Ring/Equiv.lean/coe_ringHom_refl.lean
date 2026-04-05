import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem coe_ringHom_refl : (RingEquiv.refl R : R →+* R) = RingHom.id R := rfl

