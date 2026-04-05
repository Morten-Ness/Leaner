import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized₀_smul (I : Submodule R R) : (I • M').localized₀ p f = I • M'.localized₀ p f := by
  apply le_antisymm
  · rintro _ ⟨a, ha, s, rfl⟩
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro r hr n hn
      rw [IsLocalizedModule.mk'_smul]
      exact Submodule.smul_mem_smul hr ⟨n, hn, s, rfl⟩
    · simp +contextual only [IsLocalizedModule.mk'_add, add_mem, implies_true]
  · refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨a, ha, s, rfl⟩
    rw [← IsLocalizedModule.mk'_smul]
    exact ⟨_, Submodule.smul_mem_smul hr ha, s, rfl⟩

