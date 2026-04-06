import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p := by
  rw [ringChar.eq_iff]
