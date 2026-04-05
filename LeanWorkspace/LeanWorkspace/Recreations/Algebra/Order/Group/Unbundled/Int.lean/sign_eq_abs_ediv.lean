import Mathlib

theorem sign_eq_abs_ediv (a : ℤ) : sign a = |a| / a := if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (Int.sign_mul_self_eq_abs _).symm).symm

