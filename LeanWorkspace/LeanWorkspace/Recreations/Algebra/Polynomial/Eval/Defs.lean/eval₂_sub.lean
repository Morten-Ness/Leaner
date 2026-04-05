import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem eval₂_sub {S} [Ring S] (f : R →+* S) {x : S} :
    (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x := by
  rw [sub_eq_add_neg, Polynomial.eval₂_add, Polynomial.eval₂_neg, sub_eq_add_neg]

