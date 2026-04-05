import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized'_smul (I : Submodule R R) :
    (I • M').localized' S p f = I.localized' S p (Algebra.linearMap R S) • M'.localized' S p f := Submodule.restrictScalars_injective R _ _ <| by
    simp_rw [Submodule.restrictScalars_localized'_smul, Submodule.restrictScalars_localized', Submodule.localized₀_smul]

