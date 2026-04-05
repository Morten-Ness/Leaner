import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_sum [Semiring S] (n : ℕ) (f : ℕ → R → S[X]) :
    coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n := by
  simp [Polynomial.sum]

