import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = (x⁻¹ : K) := rfl

