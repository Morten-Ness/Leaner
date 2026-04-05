import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

set_option backward.isDefEq.respectTransparency false in
theorem single_mul_single (m₁ m₂ : M) (r₁ r₂ : R) :
    single m₁ r₁ * single m₂ r₂ = single (m₁ * m₂) (r₁ * r₂) := by simp [MonoidAlgebra.mul_def]

