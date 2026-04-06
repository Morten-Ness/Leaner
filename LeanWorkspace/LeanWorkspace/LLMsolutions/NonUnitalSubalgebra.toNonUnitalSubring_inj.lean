import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommRing R]

variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]

variable [Module R A] [Module R B] [Module R C]

theorem toNonUnitalSubring_inj {S U : NonUnitalSubalgebra R A} :
    S.toNonUnitalSubring = U.toNonUnitalSubring ↔ S = U := by
  constructor
  · intro h
    ext x
    change x ∈ S.toNonUnitalSubring ↔ x ∈ U.toNonUnitalSubring
    rw [h]
  · intro h
    rw [h]
