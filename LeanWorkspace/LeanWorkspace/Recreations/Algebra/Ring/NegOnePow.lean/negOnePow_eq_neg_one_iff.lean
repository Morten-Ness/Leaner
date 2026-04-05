import Mathlib

theorem negOnePow_eq_neg_one_iff (n : ℤ) : n.negOnePow = -1 ↔ Odd n := by
  constructor
  · intro h
    rw [← Int.not_even_iff_odd]
    intro h'
    rw [Int.negOnePow_even _ h'] at h
    contradiction
  · exact Int.negOnePow_odd n

