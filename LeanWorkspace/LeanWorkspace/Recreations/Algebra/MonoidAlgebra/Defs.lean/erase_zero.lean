import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem erase_zero (m : M) : MonoidAlgebra.erase m (0 : R[M]) = 0 := by simp [MonoidAlgebra.erase]

