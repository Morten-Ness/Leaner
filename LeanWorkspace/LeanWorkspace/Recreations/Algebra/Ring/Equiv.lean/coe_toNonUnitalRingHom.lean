import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f := rfl

