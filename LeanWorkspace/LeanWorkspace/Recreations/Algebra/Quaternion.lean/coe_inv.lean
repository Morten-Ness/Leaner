import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = (↑x)⁻¹ := map_inv₀ (algebraMap R ℍ[R]) _

