import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

theorem isInteger_zero : IsLocalizedModule.IsInteger f (0 : M') := Submodule.zero_mem _

