import Mathlib

variable (R : Type u) [Ring R]

theorem ofHom_apply {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) (x : M) : ofHom f x = f x := rfl

