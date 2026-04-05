import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem charP_to_charZero [CharP R 0] : CharZero R := charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

