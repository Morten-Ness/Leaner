import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]

variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

theorem Module.FinitePresentation.linearEquivMap_symm_apply [Module.FinitePresentation R M]
    (f : M →ₗ[R] N) : (Module.FinitePresentation.linearEquivMap S).symm ((IsLocalizedModule.map S
    (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N)) f) =
    (LocalizedModule.mkLinearMap S (M →ₗ[R] N)) f := IsLocalizedModule.linearEquiv_symm_apply S _ _ f

