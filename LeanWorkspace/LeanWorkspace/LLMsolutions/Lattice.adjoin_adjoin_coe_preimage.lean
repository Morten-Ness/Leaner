FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_adjoin_coe_preimage {s : Set A} :
    Algebra.adjoin R (((↑) : Algebra.adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine top_unique ?_
  intro x hx
  rw [Algebra.mem_adjoin_iff]
  exact ⟨x, by
    change ((x : Algebra.adjoin R s) : A) ∈ s
    exact x.2, rfl⟩
