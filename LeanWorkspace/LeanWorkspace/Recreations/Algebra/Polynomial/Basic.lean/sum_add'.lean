import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_add' {S : Type*} [AddCommMonoid S] (p : R[X]) (f g : ℕ → R → S) :
    p.sum (f + g) = p.sum f + p.sum g := by simp [Polynomial.sum_def, Finset.sum_add_distrib]

