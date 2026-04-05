import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_eq_sum_range' {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : R) :
    p.eval x = ∑ i ∈ Finset.range n, p.coeff i * x ^ i := by
  rw [eval_eq_sum, p.sum_over_range' _ _ hn]; simp

