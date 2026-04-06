FAIL
import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  constructor
  · intro h
    have hb : b + b = 0 := by
      simpa [two_mul] using (CharP.cast_eq_zero (R := R) 2 b)
    have hneg : -b = b := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa [add_comm] using hb
    calc
      a = a + b + b := by rw [hb, add_zero]
      _ = c + b := by rw [h, add_assoc, hneg]
  · intro h
    have hb : b + b = 0 := by
      simpa [two_mul] using (CharP.cast_eq_zero (R := R) 2 b)
    calc
      a + b = (c + b) + b := by rw [h]
      _ = c + (b + b) := by rw [add_assoc]
      _ = c + 0 := by rw [hb]
      _ = c := by rw [add_zero]
