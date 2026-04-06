FAIL
import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_eq_mod (n : ℤ) : (n : R) = (n % 2 : ℤ) := by
  rw [← Int.mul_ediv_add_emod n 2]
  rw [Int.cast_add]
  congr 1
  · rw [Int.cast_mul]
    norm_num [CharP.cast_eq_zero_iff (R := R)]
  · rfl
