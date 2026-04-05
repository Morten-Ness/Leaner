import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x ∈ Algebra.adjoin R s) : f x ∈ Algebra.adjoin R (f '' (s ∪ {1})) := by
  induction h using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ⟨a, ⟨Set.subset_union_left ha, rfl⟩⟩
  | algebraMap r =>
    have : f 1 ∈ Algebra.adjoin R (f '' (s ∪ {1})) :=
      Algebra.subset_adjoin ⟨1, ⟨Set.subset_union_right <| Set.mem_singleton 1, rfl⟩⟩
    convert Subalgebra.smul_mem (Algebra.adjoin R (f '' (s ∪ {1}))) this r
    rw [algebraMap_eq_smul_one]
    exact f.map_smul _ _
  | add y z _ _ hy hz => simpa [hy, hz] using Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => simpa [hf, hy, hz] using Subalgebra.mul_mem _ hy hz

