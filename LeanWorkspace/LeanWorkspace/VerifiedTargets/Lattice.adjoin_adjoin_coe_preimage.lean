import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_adjoin_coe_preimage {s : Set A} : Algebra.adjoin R (((↑) : Algebra.adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun ⟨x, hx⟩ ↦
      Algebra.adjoin_induction (fun a ha ↦ ?_) (fun r ↦ ?_) (fun _ _ _ _ ↦ ?_) (fun _ _ _ _ ↦ ?_) hx
  · exact Algebra.subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _

