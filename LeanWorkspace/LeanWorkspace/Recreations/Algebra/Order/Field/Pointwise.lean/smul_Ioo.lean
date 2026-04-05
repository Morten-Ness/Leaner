import Mathlib

open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)

theorem smul_Ioo : r • Ioo a b = Ioo (r * a) (r * b) := (OrderIso.mulLeft₀ r hr).image_Ioo a b

