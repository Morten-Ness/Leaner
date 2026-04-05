import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem star_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    star z ∈ (QuadraticAlgebra R a b)⁰ ↔ z ∈ (QuadraticAlgebra R a b)⁰ := by
  refine ⟨fun h ↦ ?_, QuadraticAlgebra.star_mem_nonZeroDivisors⟩
  rw [← star_involutive z]
  exact QuadraticAlgebra.star_mem_nonZeroDivisors h

