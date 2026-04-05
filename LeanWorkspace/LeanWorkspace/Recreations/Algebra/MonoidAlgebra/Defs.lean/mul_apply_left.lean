import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Group G]

theorem mul_apply_left (x y : R[G]) (g : G) : (x * y) g = x.sum fun h r ↦ r * y (h⁻¹ * g) := by
  classical
  rw [MonoidAlgebra.mul_apply]
  dsimp [Finsupp.sum]
  congr! 1
  simp +contextual [← eq_inv_mul_iff_mul_eq]

