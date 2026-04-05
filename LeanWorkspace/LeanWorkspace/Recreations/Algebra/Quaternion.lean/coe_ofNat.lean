import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem coe_ofNat {n : ℕ} [n.AtLeastTwo] :
    ((ofNat(n) : R) : ℍ[R,c₁,c₂,c₃]) = (ofNat(n) : ℍ[R,c₁,c₂,c₃]) := rfl

