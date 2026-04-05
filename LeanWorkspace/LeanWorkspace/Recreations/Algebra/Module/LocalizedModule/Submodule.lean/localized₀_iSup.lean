import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized₀_iSup {ι : Type*} (g : ι → Submodule R M) :
    (⨆ i, g i).localized₀ p f = ⨆ i, (g i).localized₀ p f := by
  let : Module (Localization p) N := IsLocalizedModule.module p f
  have : IsScalarTower R (Localization p) N := IsLocalizedModule.isScalarTower_module p f
  simpa using congr_arg (restrictScalars R) (Submodule.localized'_iSup (Localization p) p f g)

