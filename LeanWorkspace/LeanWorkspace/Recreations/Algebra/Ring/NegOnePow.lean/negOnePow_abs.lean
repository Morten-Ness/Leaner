import Mathlib

theorem negOnePow_abs (n : ℤ) : |n|.negOnePow = n.negOnePow := by
  obtain h | h := abs_choice n <;> simp only [h, Int.negOnePow_neg]

