import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem eval_eq_smeval : p.eval r = p.smeval r := by
  rw [eval_eq_sum, Polynomial.smeval_eq_sum]
  rfl

