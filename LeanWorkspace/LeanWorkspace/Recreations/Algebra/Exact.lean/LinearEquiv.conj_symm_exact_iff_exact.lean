import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem LinearEquiv.conj_symm_exact_iff_exact (e : N' ≃ₗ[R] N) :
    Function.Exact (e.symm ∘ₗ f) (g ∘ₗ (e : N' →ₗ[R] N)) ↔ Exact f g := LinearEquiv.conj_exact_iff_exact _ _ e.symm

