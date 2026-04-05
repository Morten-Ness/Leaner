import Mathlib

theorem negOnePow_eq_one_iff (n : ℤ) : n.negOnePow = 1 ↔ Even n := by
  constructor
  · intro h
    rw [← Int.not_odd_iff_even]
    intro h'
    simp only [Int.negOnePow_odd _ h'] at h
    contradiction
  · exact Int.negOnePow_even n

