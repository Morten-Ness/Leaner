import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_def {S : Type*} [AddCommMonoid S] (p : R[X]) (f : ℕ → R → S) :
    p.sum f = ∑ n ∈ p.support, f n (p.coeff n) := rfl

