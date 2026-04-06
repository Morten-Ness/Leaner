import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

theorem of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) := by
  refine ⟨?_⟩
  intro hn
  apply h
  exact (CharP.cast_eq_zero_iff (R := R) p n).mp hn
