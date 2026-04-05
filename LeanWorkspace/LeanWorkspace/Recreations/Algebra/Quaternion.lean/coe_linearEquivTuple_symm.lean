import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem coe_linearEquivTuple_symm :
    ⇑(QuaternionAlgebra.linearEquivTuple c₁ c₂ c₃).symm = (QuaternionAlgebra.equivTuple c₁ c₂ c₃).symm := rfl

