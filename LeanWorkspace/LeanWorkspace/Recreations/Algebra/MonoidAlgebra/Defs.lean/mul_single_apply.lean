import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Group G]

theorem mul_single_apply (x : R[G]) (r : R) (g h : G) : (x * single g r) h = x (h * g⁻¹) * r := MonoidAlgebra.mul_single_apply_aux <| by simp [eq_mul_inv_iff_mul_eq]

