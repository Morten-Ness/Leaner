import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_add_self' : star a + a = ↑(2 * a.re + c₂ * a.imI) := by rw [add_comm, QuaternionAlgebra.self_add_star']

