import Mathlib

variable (R : Type u) [Semiring R]

theorem ofHom_apply {M N : Type v} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (x : M) : ofHom f x = f x := rfl

