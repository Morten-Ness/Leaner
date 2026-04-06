FAIL
import Mathlib

theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z := by
  simpa [normalize] using hz.le
