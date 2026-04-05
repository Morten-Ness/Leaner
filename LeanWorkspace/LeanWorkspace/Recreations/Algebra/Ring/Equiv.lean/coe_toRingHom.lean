import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem coe_toRingHom (f : R ≃+* S) : ⇑(f : R →+* S) = f := rfl

