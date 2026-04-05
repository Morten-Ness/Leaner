import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_ofNat (n : ℕ) [n.AtLeastTwo] (a : R) :
    (ofNat(n) : R[X]).eval a = ofNat(n) := by
  simp only [OfNat.ofNat, Polynomial.eval_natCast]

