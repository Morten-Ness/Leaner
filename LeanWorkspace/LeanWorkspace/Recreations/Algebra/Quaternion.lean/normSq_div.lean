import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem normSq_div : Quaternion.normSq (a / b) = Quaternion.normSq a / Quaternion.normSq b := map_div₀ Quaternion.normSq a b

