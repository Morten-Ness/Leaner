import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem toNonUnitalRingHom_eq_coe (f : R ≃+* S) : f.toNonUnitalRingHom = ↑f := rfl

