FAIL
import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

theorem not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  intro hk
  rcases hk with ⟨m, hm⟩
  subst hm
  exact h.ne (by rw [Nat.cast_mul, CharP.cast_eq_zero, zero_nsmul])
