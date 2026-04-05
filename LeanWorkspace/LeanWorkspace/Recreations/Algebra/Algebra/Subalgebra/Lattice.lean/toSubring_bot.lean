import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubring_bot (A : Type*) [CommRing A] (R : Subring A) :
    (⊥ : Subalgebra R A).toSubring = R := by
  aesop (add norm Subalgebra.mem_carrier.symm)

