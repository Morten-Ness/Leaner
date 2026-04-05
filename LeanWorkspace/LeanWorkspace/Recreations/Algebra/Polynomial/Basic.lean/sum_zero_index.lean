import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_zero_index {S : Type*} [AddCommMonoid S] (f : ℕ → R → S) : (0 : R[X]).sum f = 0 := by
  simp [Polynomial.sum]

