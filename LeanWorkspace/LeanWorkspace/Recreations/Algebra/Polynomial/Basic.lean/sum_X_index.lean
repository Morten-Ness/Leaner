import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_X_index {S : Type*} [AddCommMonoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
    (Polynomial.X : R[X]).sum f = f 1 1 := Polynomial.sum_monomial_index 1 f hf

