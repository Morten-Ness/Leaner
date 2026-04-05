import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem normSq_ratCast (q : ℚ) : Quaternion.normSq (q : ℍ[R]) = (q : ℍ[R]) ^ 2 := by
  rw [← coe_ratCast, Quaternion.normSq_coe, Quaternion.coe_pow]

