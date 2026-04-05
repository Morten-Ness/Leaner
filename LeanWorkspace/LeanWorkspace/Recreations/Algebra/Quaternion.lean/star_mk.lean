import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_mk (a₁ a₂ a₃ a₄ : R) : star (QuaternionAlgebra.mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) =
    ⟨a₁ + c₂ * a₂, -a₂, -a₃, -a₄⟩ := rfl

