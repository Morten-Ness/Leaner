import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid N]
  [AddCommMonoid N'] [AddCommMonoid P] [AddCommMonoid P'] [Module R M]
  [Module R M'] [Module R N] [Module R N'] [Module R P] [Module R P']

variable {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Exact.linearMap_comp_eq_zero (h : Exact f g) : g.comp f = 0 := DFunLike.coe_injective h.comp_eq_zero

