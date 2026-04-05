import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Add R]

theorem coe_addEquivTuple (c₁ c₂ c₃ : R) : ⇑(QuaternionAlgebra.addEquivTuple c₁ c₂ c₃) = QuaternionAlgebra.equivTuple c₁ c₂ c₃ := rfl

