import Mathlib

open scoped Pointwise

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b r : K} (hr : 0 < r)

theorem smul_Iio : r • Iio a = Iio (r * a) := (OrderIso.mulLeft₀ r hr).image_Iio a

