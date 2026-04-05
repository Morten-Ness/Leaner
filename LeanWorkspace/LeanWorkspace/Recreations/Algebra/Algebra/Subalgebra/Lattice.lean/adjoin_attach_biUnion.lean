import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_attach_biUnion [DecidableEq A] {α : Type*} {s : Finset α} (f : s → Finset A) :
    Algebra.adjoin R (s.attach.biUnion f : Set A) = ⨆ x, Algebra.adjoin R (f x) := by simp [Algebra.adjoin_iUnion]

