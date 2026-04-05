import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized'_eq_span : Submodule.localized' S p f M' = span S (f '' M') := by
  refine le_antisymm ?_ (span_le.mpr <| by rintro _ ⟨m, hm, rfl⟩; exact ⟨m, hm, 1, by simp⟩)
  rintro _ ⟨m, hm, s, rfl⟩
  rw [← one_smul R m, ← mul_one s, ← IsLocalizedModule.mk'_smul_mk' S]
  exact smul_mem _ _ (subset_span ⟨m, hm, by simp⟩)

