import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval x := Polynomial.eval₂_neg _

