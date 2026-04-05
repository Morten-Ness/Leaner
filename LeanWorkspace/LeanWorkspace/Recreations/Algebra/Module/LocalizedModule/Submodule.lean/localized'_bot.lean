import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized'_bot : (⊥ : Submodule R M).localized' S p f = ⊥ := SetLike.ext' (by apply SetLike.ext'_iff.mp <| Submodule.localized₀_bot p f)

