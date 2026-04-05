import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_listSum (l : List R[X]) (x : R) : Polynomial.eval x l.sum = (l.map (Polynomial.eval x)).sum := Polynomial.eval₂_list_sum ..

