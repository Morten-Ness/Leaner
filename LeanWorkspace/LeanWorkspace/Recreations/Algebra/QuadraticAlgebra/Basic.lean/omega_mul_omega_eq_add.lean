import Mathlib

variable {R : Type*} {a b : R}

variable [CommSemiring R]

theorem omega_mul_omega_eq_add :
    (ω : QuadraticAlgebra R a b) * ω = a • 1 + b • ω := by
  ext <;> simp

