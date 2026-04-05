import Mathlib

variable {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

variable (S : Subalgebra R A)

theorem mem_toNonUnitalSubalgebra {S : Subalgebra R A} {x : A} :
    x ∈ S.toNonUnitalSubalgebra ↔ x ∈ S := Iff.rfl

