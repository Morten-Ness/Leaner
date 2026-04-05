import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

theorem isInteger_add {x y : M'} (hx : IsLocalizedModule.IsInteger f x) (hy : IsLocalizedModule.IsInteger f y) : IsLocalizedModule.IsInteger f (x + y) := Submodule.add_mem _ hx hy

