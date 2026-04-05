import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem mul_def (x y : R[M]) :
    x * y = x.sum fun m₁ r₁ ↦ y.sum fun m₂ r₂ ↦ single (m₁ * m₂) (r₁ * r₂) := by
  with_unfolding_all rfl

