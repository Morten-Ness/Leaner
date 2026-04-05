import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_C_index {a} {β} [AddCommMonoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
    (Polynomial.C a).sum f = f 0 a := Polynomial.sum_monomial_index a f h

-- the assumption `hf` is only necessary when the ring is trivial

