import Mathlib

variable {R : Type*} {a b : R}

variable [CommSemiring R]

theorem omega_mul_algebraMap_mul_mk (n x y : R) :
    (ω : QuadraticAlgebra R a b) * algebraMap _ _ n * ⟨x, y⟩ = ⟨a * n * y, n * x + n * b * y⟩ := by
  ext <;> simp; ring

