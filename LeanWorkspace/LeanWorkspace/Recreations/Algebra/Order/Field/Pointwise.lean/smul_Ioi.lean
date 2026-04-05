import Mathlib

open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)

theorem smul_Ioi : r • Ioi a = Ioi (r * a) := (OrderIso.mulLeft₀ r hr).image_Ioi a

