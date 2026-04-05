import Mathlib

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

theorem smeval_natCast (n : ℕ) : (n : R[X]).smeval x = n • x ^ 0 := by
  induction n with
  | zero => simp only [Polynomial.smeval_zero, Nat.cast_zero, zero_smul]
  | succ n ih => rw [n.cast_succ, Polynomial.smeval_add, ih, Polynomial.smeval_one, ← add_nsmul]

