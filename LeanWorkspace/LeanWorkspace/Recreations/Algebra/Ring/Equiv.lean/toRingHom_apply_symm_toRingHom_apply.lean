import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toRingHom_apply_symm_toRingHom_apply (e : R ≃+* S) :
    ∀ y : S, e.toRingHom (e.symm.toRingHom y) = y := RingEquiv.apply_symm_apply e.toEquiv

