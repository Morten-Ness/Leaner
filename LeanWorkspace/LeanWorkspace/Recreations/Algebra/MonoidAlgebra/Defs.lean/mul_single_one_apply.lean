import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem mul_single_one_apply (x : R[M]) (r : R) (m : M) : (x * single 1 r : R[M]) m = x m * r := MonoidAlgebra.mul_single_apply_aux x (by simp)

