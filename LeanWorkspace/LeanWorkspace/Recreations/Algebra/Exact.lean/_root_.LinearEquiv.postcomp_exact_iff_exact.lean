import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem _root_.LinearEquiv.postcomp_exact_iff_exact {e : P ≃ₗ[R] P'} :
    Exact f ((e : P →ₗ[R] P') ∘ₗ g) ↔ Exact f g := e.injective.comp_exact_iff_exact

