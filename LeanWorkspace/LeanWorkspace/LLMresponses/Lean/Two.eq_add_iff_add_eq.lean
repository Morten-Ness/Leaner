import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  constructor
  · intro h
    calc
      a + c = (b + c) + c := by rw [h]
      _ = b + (c + c) := by rw [add_assoc]
      _ = b + 0 := by rw [CharTwo.add_self_eq_zero]
      _ = b := by rw [add_zero]
  · intro h
    calc
      a = (a + c) + c := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = b + c := by rw [h]
