import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized'_iSup {ι : Type*} (g : ι → Submodule R M) :
    (⨆ i, g i).localized' S p f = ⨆ i, (g i).localized' S p f := by
  exact GaloisConnection.l_iSup (Submodule.localized'gi S p f).gc

