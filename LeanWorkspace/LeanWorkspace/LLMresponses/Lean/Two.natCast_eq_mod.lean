FAIL
import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_eq_mod (n : ℕ) : (n : R) = (n % 2 : ℕ) := by
  rw [← Nat.mod_add_div n 2]
  norm_num
  rw [Nat.cast_add]
  have h : ((2 * (n / 2) : ℕ) : R) = 0 := by
    rw [Nat.cast_mul]
    norm_num
  rw [h, zero_add]
