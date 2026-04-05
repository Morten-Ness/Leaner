import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem normSq_zpow (z : ℤ) : Quaternion.normSq (a ^ z) = Quaternion.normSq a ^ z := map_zpow₀ Quaternion.normSq a z

