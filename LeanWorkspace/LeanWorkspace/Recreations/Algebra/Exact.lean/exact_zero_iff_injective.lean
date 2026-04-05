import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]

theorem exact_zero_iff_injective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M →ₗ[R] N) :
    Function.Exact (0 : P →ₗ[R] M) f ↔ Function.Injective f := by
  simp [← ker_eq_bot, LinearMap.exact_iff]

