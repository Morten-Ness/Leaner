import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem _root_.LinearEquiv.precomp_exact_iff_exact {e : M' ≃ₗ[R] M} :
    Exact (f ∘ₗ (e : M' →ₗ[R] M)) g ↔ Exact f g := e.surjective.comp_exact_iff_exact

