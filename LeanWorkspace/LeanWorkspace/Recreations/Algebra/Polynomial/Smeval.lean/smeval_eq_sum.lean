import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem smeval_eq_sum : p.smeval x = p.sum (Polynomial.smul_pow x) := by rw [smeval_def]

