import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']

theorem toNonUnitalRingHom_injective :
    Function.Injective (RingEquiv.toNonUnitalRingHom : R ≃+* S → R →ₙ+* S) := fun _ _ h =>
  RingEquiv.ext (NonUnitalRingHom.ext_iff.1 h)

