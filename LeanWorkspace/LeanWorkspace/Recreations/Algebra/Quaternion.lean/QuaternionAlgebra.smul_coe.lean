import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem smul_coe : x • (y : ℍ[R,c₁,c₂,c₃]) = ↑(x * y) := by rw [QuaternionAlgebra.coe_mul, QuaternionAlgebra.coe_mul_eq_smul]

