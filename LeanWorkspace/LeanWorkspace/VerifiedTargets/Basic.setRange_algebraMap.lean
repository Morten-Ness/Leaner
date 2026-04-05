import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem setRange_algebraMap {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S : Subalgebra R A) : Set.range (algebraMap S A) = (S : Set A) := SetLike.ext'_iff.mp S.rangeS_algebraMap

