import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem natCast_eq_natCast' (h : a ≡ b [MOD p]) : (a : R) = b := by
  wlog hle : a ≤ b
  · exact (this R p h.symm (le_of_not_ge hle)).symm
  rw [Nat.modEq_iff_dvd' hle] at h
  rw [← Nat.sub_add_cancel hle, Nat.cast_add, (cast_eq_zero_iff R p _).mpr h, zero_add]

