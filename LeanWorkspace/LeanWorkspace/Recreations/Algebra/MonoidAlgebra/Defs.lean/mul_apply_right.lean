import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Group G]

theorem mul_apply_right (x y : R[G]) (g : G) : (x * y) g = y.sum fun h r ↦ x (g * h⁻¹) * r := by
  classical
  rw [MonoidAlgebra.mul_apply, Finsupp.sum_comm]
  dsimp [Finsupp.sum]
  congr! 1
  simp +contextual [← eq_mul_inv_iff_mul_eq]

