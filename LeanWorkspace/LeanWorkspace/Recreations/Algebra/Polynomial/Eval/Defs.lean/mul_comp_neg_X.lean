import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_comp_neg_X {R : Type*} [Ring R] (p q : R[X]) :
    (p * q).comp (-Polynomial.X) = p.comp (-Polynomial.X) * q.comp (-Polynomial.X) := Polynomial.eval₂_mul_noncomm Polynomial.C (-Polynomial.X) fun _ ↦ Commute.symm (commute_X _).neg_left

