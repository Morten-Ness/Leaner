import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem eval₂_neg {S} [Ring S] (f : R →+* S) {x : S} : (-p).eval₂ f x = -p.eval₂ f x := by
  rw [eq_neg_iff_add_eq_zero, ← Polynomial.eval₂_add, neg_add_cancel, Polynomial.eval₂_zero]

