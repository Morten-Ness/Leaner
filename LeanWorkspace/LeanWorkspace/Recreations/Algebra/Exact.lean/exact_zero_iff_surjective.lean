import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem exact_zero_iff_surjective {M N : Type*} (P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommMonoid P] [Module R N] [Module R M]
    [Module R P] (f : M →ₗ[R] N) :
    Function.Exact f (0 : N →ₗ[R] P) ↔ Function.Surjective f := by
  simp [← range_eq_top, LinearMap.exact_iff, eq_comm]

