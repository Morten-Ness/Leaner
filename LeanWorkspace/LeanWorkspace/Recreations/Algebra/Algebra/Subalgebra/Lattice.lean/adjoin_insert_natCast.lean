import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_natCast (n : ℕ) (s : Set A) : Algebra.adjoin R (insert (n : A) s) = Algebra.adjoin R s := mod_cast Algebra.adjoin_insert_algebraMap (n : R) s

