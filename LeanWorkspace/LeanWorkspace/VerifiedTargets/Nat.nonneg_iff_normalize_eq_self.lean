import Mathlib

theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z := ⟨Int.nonneg_of_normalize_eq_self, Int.normalize_of_nonneg⟩

