import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toRingHom_comp_symm_toRingHom (e : R ≃+* S) :
    e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := by
  simp

