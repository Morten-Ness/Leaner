import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]

variable (f' : P →ₗ[R] Q) [IsLocalizedModule p f']

include S in
theorem toKerLocalized_isLocalizedModule (g : M →ₗ[R] P) :
    IsLocalizedModule p (LinearMap.toKerIsLocalized p f f' g) := let e : Submodule.localized' S p f (ker g) ≃ₗ[S]
      ker ((map p f f' g).extendScalarsOfIsLocalization p S) :=
    LinearEquiv.ofEq _ _ (LinearMap.localized'_ker_eq_ker_localizedMap S p f f' g)
  IsLocalizedModule.of_linearEquiv p (Submodule.toLocalized' S p f (ker g)) (e.restrictScalars R)

