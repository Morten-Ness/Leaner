import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem Monic.ne_zero_of_ne (h : (0 : R) ≠ 1) {p : R[X]} (hp : p.Monic) : p ≠ 0 := by
  nontriviality R
  exact hp.ne_zero

