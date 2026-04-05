import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem CharP.eq ringExpChar (q : ℕ) [h : ExpChar R q] : ringExpChar R = q := by
  rcases h with _ | h
  · haveI := CharP.ofCharZero R
    rw [ringExpChar, CharP.eq ringChar R 0]; rfl
  rw [ringExpChar, CharP.eq ringChar R q]
  exact Nat.max_eq_left h.one_lt.le

