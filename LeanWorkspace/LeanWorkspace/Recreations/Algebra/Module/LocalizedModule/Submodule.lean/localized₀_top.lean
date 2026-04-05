import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized₀_top : (⊤ : Submodule R M).localized₀ p f = ⊤ := by
  rw [← top_le_iff]
  rintro x _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p f x
  exact ⟨x, trivial, s, rfl⟩

