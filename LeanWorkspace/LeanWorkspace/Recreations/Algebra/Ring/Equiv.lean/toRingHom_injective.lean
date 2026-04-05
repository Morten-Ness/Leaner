import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring S']

theorem toRingHom_injective : Function.Injective (RingEquiv.toRingHom : R ≃+* S → R →+* S) := fun _ _ h =>
  RingEquiv.ext (RingHom.ext_iff.1 h)

