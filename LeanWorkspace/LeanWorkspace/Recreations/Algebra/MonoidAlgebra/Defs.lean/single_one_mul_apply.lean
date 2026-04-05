import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem single_one_mul_apply (x : R[M]) (r : R) (m : M) : (single 1 r * x : R[M]) m = r * x m := MonoidAlgebra.single_mul_apply_aux x (by simp)

