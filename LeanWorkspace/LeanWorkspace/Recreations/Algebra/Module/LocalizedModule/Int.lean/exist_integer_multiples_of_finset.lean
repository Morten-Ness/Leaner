import Mathlib

variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

variable [IsLocalizedModule S f]

theorem exist_integer_multiples_of_finset (s : Finset M') :
    ∃ b : S, ∀ a ∈ s, IsLocalizedModule.IsInteger f ((b : R) • a) := IsLocalizedModule.exist_integer_multiples S f s id

