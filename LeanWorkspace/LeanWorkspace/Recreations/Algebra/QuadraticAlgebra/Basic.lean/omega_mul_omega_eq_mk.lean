import Mathlib

variable {R : Type*} {a b : R}

variable [CommSemiring R]

theorem omega_mul_omega_eq_mk : (ω : QuadraticAlgebra R a b) * ω = ⟨a, b⟩ := by
  ext <;> simp

