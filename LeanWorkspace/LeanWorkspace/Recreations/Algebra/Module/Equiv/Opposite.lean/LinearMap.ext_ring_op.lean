import Mathlib

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]

theorem LinearMap.ext_ring_op
    {σ : Rᵐᵒᵖ →+* S} {f g : R →ₛₗ[σ] M} (h : f (1 : R) = g (1 : R)) :
    f = g := ext fun x ↦ by
    rw [← one_mul x, ← op_smul_eq_mul, f.map_smulₛₗ, h, g.map_smulₛₗ]

