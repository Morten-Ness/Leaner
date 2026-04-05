import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]) :
    (p * q).comp r = p.comp r * q.comp r := Polynomial.eval₂_mul _ _

