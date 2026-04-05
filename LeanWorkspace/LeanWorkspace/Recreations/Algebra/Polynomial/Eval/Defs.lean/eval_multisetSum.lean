import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_multisetSum (s : Multiset R[X]) (x : R) : Polynomial.eval x s.sum = (s.map (Polynomial.eval x)).sum := Polynomial.eval₂_multiset_sum ..

