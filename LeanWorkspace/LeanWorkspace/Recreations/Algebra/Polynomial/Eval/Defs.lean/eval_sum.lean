import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_sum (p : R[X]) (f : ℕ → R → R[X]) (x : R) :
    (p.sum f).eval x = p.sum fun n a => (f n a).eval x := Polynomial.eval₂_sum _ _ _ _

