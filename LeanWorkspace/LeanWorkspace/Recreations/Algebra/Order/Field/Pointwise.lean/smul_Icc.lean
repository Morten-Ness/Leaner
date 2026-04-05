import Mathlib

open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)

theorem smul_Icc : r • Icc a b = Icc (r * a) (r * b) := (OrderIso.mulLeft₀ r hr).image_Icc a b

