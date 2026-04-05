import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

theorem FinitePresentation.of_isBaseChange
    {A} [CommRing A] [Algebra R A] [Module A N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) (h : IsBaseChange A f) [Module.FinitePresentation R M] :
    Module.FinitePresentation A N := Module.finitePresentation_of_surjective
    h.equiv.toLinearMap h.equiv.surjective (by simpa using Submodule.fg_bot)

