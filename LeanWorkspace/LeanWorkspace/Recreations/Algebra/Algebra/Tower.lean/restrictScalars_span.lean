import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

theorem restrictScalars_span (hsur : Function.Surjective (algebraMap R A)) (X : Set M) :
    AlgHom.restrictScalars R (span A X) = span R X := by
  refine ((span_le_restrictScalars R A X).antisymm fun m hm => ?_).symm
  refine span_induction subset_span (zero_mem _) (fun _ _ _ _ => add_mem) (fun a m _ hm => ?_) hm
  obtain ⟨r, rfl⟩ := hsur a
  simpa [IsScalarTower.algebraMap_smul] using smul_mem _ r hm

