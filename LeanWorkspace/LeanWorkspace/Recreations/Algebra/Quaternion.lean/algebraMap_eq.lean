import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem algebraMap_eq (r : R) : algebraMap R ℍ[R,c₁,c₂,c₃] r = ⟨r, 0, 0, 0⟩ := rfl

