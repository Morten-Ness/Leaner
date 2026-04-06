import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommRing R]

variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]

variable [Module R A] [Module R B] [Module R C]

theorem toNonUnitalSubring_injective :
    Function.Injective (NonUnitalSubalgebra.toNonUnitalSubring : NonUnitalSubalgebra R A → NonUnitalSubring A) :=
by
  intro S T h
  ext x
  exact SetLike.ext_iff.mp h x
