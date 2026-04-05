import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ Algebra.adjoin R s) : Algebra.adjoin R s = S := le_antisymm (Algebra.adjoin_le h₁) h₂

