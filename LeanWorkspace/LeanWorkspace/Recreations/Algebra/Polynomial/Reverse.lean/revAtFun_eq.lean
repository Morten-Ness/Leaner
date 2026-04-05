import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAtFun_eq (N i : ℕ) : Polynomial.revAtFun N i = Polynomial.revAt N i := rfl

