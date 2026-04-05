import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R]

theorem expChar_ne_zero (p : ℕ) [hR : ExpChar R p] : p ≠ 0 := by
  cases hR
  · exact one_ne_zero
  · exact ‹p.Prime›.ne_zero

