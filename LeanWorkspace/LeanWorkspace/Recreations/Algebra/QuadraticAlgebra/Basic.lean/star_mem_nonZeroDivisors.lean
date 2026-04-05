import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem star_mem_nonZeroDivisors {z : QuadraticAlgebra R a b}
    (hz : z ∈ (QuadraticAlgebra R a b)⁰) :
    star z ∈ (QuadraticAlgebra R a b)⁰ := by
  rw [mem_nonZeroDivisors_iff_right] at hz ⊢
  intro w hw
  apply star_involutive.injective
  rw [star_zero]
  apply hz
  rw [← star_involutive z, ← star_mul, mul_comm, hw, star_zero]

