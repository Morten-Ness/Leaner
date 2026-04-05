import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem mul_coe_eq_smul : a * r = r • a := by rw [← QuaternionAlgebra.coe_commutes, QuaternionAlgebra.coe_mul_eq_smul]

