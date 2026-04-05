import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

theorem map_integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) :
    f (IsLocalizedModule.integerMultiple S f s g i) = IsLocalizedModule.commonDenom S f s g • g i := ((IsLocalizedModule.exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec

