import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem self_add_star : a + star a = 2 * a.re + c₂ * a.imI := by simp [QuaternionAlgebra.self_add_star']

