import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem symm_toNonUnitalRingHom_comp_toNonUnitalRingHom (e : R ≃+* S) :
    e.symm.toNonUnitalRingHom.comp e.toNonUnitalRingHom = NonUnitalRingHom.id _ := by
  ext
  simp

