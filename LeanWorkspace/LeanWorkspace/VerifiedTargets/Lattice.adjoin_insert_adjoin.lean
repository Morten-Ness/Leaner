import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_adjoin (x : A) : Algebra.adjoin R (insert x ↑(Algebra.adjoin R s)) = Algebra.adjoin R (insert x s) := le_antisymm
    (Algebra.adjoin_le
      (Set.insert_subset_iff.mpr
        ⟨Algebra.subset_adjoin (Set.mem_insert _ _), Algebra.adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))

