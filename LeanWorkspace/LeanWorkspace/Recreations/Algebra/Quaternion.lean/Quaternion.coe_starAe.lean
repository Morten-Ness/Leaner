import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_starAe : ⇑(Quaternion.starAe : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ star := rfl

