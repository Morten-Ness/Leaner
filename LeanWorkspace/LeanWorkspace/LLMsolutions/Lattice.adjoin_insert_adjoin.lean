import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B]
variable [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_adjoin (x : A) :
    Algebra.adjoin R (insert x ↑(Algebra.adjoin R s)) =
      Algebra.adjoin R (insert x s) := by
  rw [Algebra.adjoin_insert_adjoin]
