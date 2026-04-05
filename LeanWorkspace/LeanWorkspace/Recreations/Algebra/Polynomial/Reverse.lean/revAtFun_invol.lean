import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAtFun_invol {N i : ℕ} : Polynomial.revAtFun N (Polynomial.revAtFun N i) = i := by
  unfold Polynomial.revAtFun
  grind

