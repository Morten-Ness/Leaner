import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_sInf : Algebra.adjoin R s = sInf { p : Subalgebra R A | s ⊆ p } := le_antisymm (le_sInf fun _ h => Algebra.adjoin_le h) (sInf_le Algebra.subset_adjoin)

