import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

variable {S : NonUnitalSubalgebra R A}

theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (S : NonUnitalSubalgebra R A) :
    NonUnitalSubringClass.subtype S = NonUnitalSubalgebraClass.subtype (R := R) S :=
  rfl

