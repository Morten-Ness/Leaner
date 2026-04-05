import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Group G]

theorem single_mul_apply (x : R[G]) (r : R) (g h : G) : (single g r * x) h = r * x (g⁻¹ * h) := MonoidAlgebra.single_mul_apply_aux <| by simp [eq_inv_mul_iff_mul_eq]

