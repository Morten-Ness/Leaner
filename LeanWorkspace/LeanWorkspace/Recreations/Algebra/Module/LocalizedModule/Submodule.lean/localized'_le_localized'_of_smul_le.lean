import Mathlib

variable {R S M N : Type*}

variable (S) [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid N]

variable [Module R M] [Module R N] [Algebra R S] [Module S N] [IsScalarTower R S N]

variable (p : Submonoid R) [IsLocalization p S] (f : M →ₗ[R] N) [IsLocalizedModule p f]

variable (M' M'' : Submodule R M)

theorem localized'_le_localized'_of_smul_le {P Q : Submodule R M} (x : p) (h : x • P ≤ Q) :
    P.localized' S p f ≤ Q.localized' S p f := Submodule.localized₀_le_localized₀_of_smul_le p f x h

