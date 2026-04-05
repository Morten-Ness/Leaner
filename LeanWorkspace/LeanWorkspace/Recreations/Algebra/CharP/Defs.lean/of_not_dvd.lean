import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

theorem of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) := ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

