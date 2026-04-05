import Mathlib

variable {R : Type*}

variable [Field R] (a b : ℍ[R])

variable [LinearOrder R] [IsStrictOrderedRing R] (a b : ℍ[R])

theorem coe_zpow (x : R) (z : ℤ) : ((x ^ z : R) : ℍ[R]) = (x : ℍ[R]) ^ z := map_zpow₀ (algebraMap R ℍ[R]) x z

