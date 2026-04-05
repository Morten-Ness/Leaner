import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem coe_starAe : ⇑(QuaternionAlgebra.starAe : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] _) = op ∘ star := rfl

