import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n := by
  rw [add_comm]
  exact Polynomial.natDegree_add_le_iff_left _ _ pn

-- TODO: Do we really want the following two lemmas? They are straightforward consequences of a
-- more atomic lemma

