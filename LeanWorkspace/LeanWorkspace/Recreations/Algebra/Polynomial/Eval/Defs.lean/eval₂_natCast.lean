import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

theorem eval₂_natCast (n : ℕ) : (n : R[X]).eval₂ f x = n := by
  induction n with
  | zero => simp only [Polynomial.eval₂_zero, Nat.cast_zero]
  | succ n ih => rw [n.cast_succ, Polynomial.eval₂_add, ih, Polynomial.eval₂_one, n.cast_succ]

