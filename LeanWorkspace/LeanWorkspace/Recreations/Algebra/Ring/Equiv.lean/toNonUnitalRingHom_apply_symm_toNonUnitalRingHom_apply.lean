import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem toNonUnitalRingHom_apply_symm_toNonUnitalRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toNonUnitalRingHom (e.symm.toNonUnitalRingHom y) = y := RingEquiv.apply_symm_apply e.toEquiv

