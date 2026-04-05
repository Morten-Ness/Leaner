import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_monomial_index {S : Type*} [AddCommMonoid S] {n : ℕ} (a : R) (f : ℕ → R → S)
    (hf : f n 0 = 0) : (Polynomial.monomial n a : R[X]).sum f = f n a := Finsupp.sum_single_index hf

