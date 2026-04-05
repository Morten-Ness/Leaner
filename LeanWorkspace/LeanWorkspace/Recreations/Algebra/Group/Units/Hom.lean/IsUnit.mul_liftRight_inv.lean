import Mathlib

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem mul_liftRight_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 := Units.mul_liftRight_inv (by intro; rfl) x

