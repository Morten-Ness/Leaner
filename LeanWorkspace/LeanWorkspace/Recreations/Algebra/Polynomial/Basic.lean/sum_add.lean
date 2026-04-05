import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_add {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g := Polynomial.sum_add' _ _ _

