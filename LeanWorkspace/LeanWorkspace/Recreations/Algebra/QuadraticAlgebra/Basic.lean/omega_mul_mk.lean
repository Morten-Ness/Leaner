import Mathlib

variable {R : Type*} {a b : R}

variable [CommSemiring R]

theorem omega_mul_mk (x y : R) : (ω : QuadraticAlgebra R a b) * ⟨x, y⟩ = ⟨a * y, x + b * y⟩ := by
  ext <;> simp

