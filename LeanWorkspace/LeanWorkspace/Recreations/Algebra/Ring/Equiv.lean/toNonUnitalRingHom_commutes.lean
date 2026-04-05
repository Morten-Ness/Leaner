import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toNonUnitalRingHom_commutes (f : R ≃+* S) :
    ((f : R →+* S) : R →ₙ+* S) = (f : R →ₙ+* S) := rfl

