import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem coe_zpow (x : { x : K // 0 < x }) (n : ℤ) : ↑(x ^ n) = (x : K) ^ n := rfl

