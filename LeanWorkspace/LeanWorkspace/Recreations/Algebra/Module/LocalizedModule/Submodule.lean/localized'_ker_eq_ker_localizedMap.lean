import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]

variable (f' : P →ₗ[R] Q) [IsLocalizedModule p f']

theorem localized'_ker_eq_ker_localizedMap (g : M →ₗ[R] P) :
    (ker g).localized' S p f = ker ((map p f f' g).extendScalarsOfIsLocalization p S) := SetLike.ext (by apply SetLike.ext_iff.mp (LinearMap.ker_localizedMap_eq_localized₀_ker f p f' g).symm)

