FAIL
import Mathlib

variable {m n : ℤ}

theorem ediv_two_mul_two_of_even : Even n → n / 2 * 2 = n := by
  intro hn
  simpa [Int.ediv_two_of_even hn] using congrArg (fun t : ℤ => t * 2) (Int.ediv_two_eq_half n)
