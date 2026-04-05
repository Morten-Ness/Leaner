import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem not_isUnit_X_pow_sub_one (R : Type*) [Ring R] [Nontrivial R] (n : ℕ) :
    ¬IsUnit (Polynomial.X ^ n - 1 : R[X]) := by
  intro h
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp at h
  apply hn
  rw [← @natDegree_one R, ← (Polynomial.monic_X_pow_sub_C _ hn).eq_one_of_isUnit h, natDegree_X_pow_sub_C]

