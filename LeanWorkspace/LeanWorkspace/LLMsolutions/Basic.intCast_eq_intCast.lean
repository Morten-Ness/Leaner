FAIL
import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [Int.modEq_iff_dvd]
  constructor
  · intro h
    have hz : ((b - a : ℤ) : R) = 0 := by
      simpa [sub_eq_add_neg] using sub_eq_zero.mpr h
    exact (CharP.intCast_eq_zero_iff (R := R) p (b - a)).mp hz
  · intro h
    have hz : ((b - a : ℤ) : R) = 0 := (CharP.intCast_eq_zero_iff (R := R) p (b - a)).mpr h
    have hs : (b : R) - a = 0 := by
      simpa [sub_eq_add_neg] using hz
    exact sub_eq_zero.mp hs
