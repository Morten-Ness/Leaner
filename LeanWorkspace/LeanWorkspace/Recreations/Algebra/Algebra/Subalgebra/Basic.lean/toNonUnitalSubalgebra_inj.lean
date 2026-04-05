import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem toNonUnitalSubalgebra_inj {S U : Subalgebra R A} :
    S.toNonUnitalSubalgebra = U.toNonUnitalSubalgebra ↔ S = U := Subalgebra.toNonUnitalSubalgebra_injective.eq_iff

