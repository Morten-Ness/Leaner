import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem algebraMap_injective : (algebraMap R ℍ[R,c₁,c₂,c₃] : _ → _).Injective := fun _ _ ↦ by simp [QuaternionAlgebra.algebraMap_eq]

