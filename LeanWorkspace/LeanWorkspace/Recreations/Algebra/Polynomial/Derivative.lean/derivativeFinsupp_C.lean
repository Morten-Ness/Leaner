import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivativeFinsupp_C (r : R) : Polynomial.derivativeFinsupp (Polynomial.C r : R[X]) = .single 0 (Polynomial.C r) := by
  ext i : 1
  match i with
  | 0 => simp
  | i + 1 => simp

