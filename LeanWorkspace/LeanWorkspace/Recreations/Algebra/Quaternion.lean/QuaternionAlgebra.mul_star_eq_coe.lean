import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem mul_star_eq_coe : a * star a = (a * star a).re := by
  rw [← star_comm_self']
  exact QuaternionAlgebra.star_mul_eq_coe a

