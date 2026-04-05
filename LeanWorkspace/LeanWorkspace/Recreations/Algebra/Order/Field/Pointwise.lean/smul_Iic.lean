import Mathlib

open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)

theorem smul_Iic : r • Iic a = Iic (r * a) := (OrderIso.mulLeft₀ r hr).image_Iic a

