import Mathlib

open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)

theorem smul_Ici : r • Ici a = Ici (r * a) := (OrderIso.mulLeft₀ r hr).image_Ici a

