import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem coe_addMonoidHom_refl : (RingEquiv.refl R : R →+ R) = AddMonoidHom.id R := rfl

