import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommRing R]

variable [NonUnitalNonAssocRing A] [NonUnitalNonAssocRing B] [NonUnitalNonAssocRing C]

variable [Module R A] [Module R B] [Module R C]

theorem coe_toNonUnitalSubring (S : NonUnitalSubalgebra R A) :
    (↑S.toNonUnitalSubring : Set A) = S := rfl

