import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] (f : R →+* S) (x : S)

theorem eval₂_eq_sum_range' (f : R →+* S) {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    eval₂ f x p = ∑ i ∈ Finset.range n, f (p.coeff i) * x ^ i := by
  rw [eval₂_eq_sum, p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero, zero_mul]

