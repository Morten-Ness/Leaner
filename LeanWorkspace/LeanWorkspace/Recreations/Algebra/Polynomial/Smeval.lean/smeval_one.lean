import Mathlib

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

theorem smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0 := by
  rw [← C_1, Polynomial.smeval_C]
  simp only [one_smul]

