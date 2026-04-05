import Mathlib

theorem sign_eq_ediv_abs' (a : ℤ) : sign a = a / |a| := if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (Int.sign_mul_abs _).symm).symm

