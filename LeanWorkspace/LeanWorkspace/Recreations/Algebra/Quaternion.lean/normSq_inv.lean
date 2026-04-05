import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem normSq_inv : Quaternion.normSq a⁻¹ = (Quaternion.normSq a)⁻¹ := map_inv₀ Quaternion.normSq _

