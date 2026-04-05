import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_algebraMap (x : R) (s : Set A) :
    Algebra.adjoin R (insert (algebraMap R A x) s) = Algebra.adjoin R s := by
  rw [Set.insert_eq, Algebra.adjoin_union]
  simp

