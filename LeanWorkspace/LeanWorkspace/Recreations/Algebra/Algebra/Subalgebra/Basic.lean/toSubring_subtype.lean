import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toSubring_subtype {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subalgebra R A) :
    S.toSubring.subtype = (S.val : S →+* A) := rfl

