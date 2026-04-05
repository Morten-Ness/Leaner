import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAt_invol {N i : ℕ} : (Polynomial.revAt N) (Polynomial.revAt N i) = i := Polynomial.revAtFun_invol

