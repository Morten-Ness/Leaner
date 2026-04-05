import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_update_le (p : R[X]) (n : ℕ) (a : R) : Polynomial.degree (p.update n a) ≤ max (Polynomial.degree p) n := by
  classical
  rw [Polynomial.degree, support_update]
  split_ifs
  · exact (Finset.max_mono (erase_subset _ _)).trans (le_max_left _ _)
  · rw [max_insert, max_comm]
    exact le_rfl

