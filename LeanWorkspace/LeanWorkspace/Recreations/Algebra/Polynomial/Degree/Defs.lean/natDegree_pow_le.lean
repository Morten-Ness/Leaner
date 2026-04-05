import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem natDegree_pow_le {p : R[X]} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  induction n with
  | zero => simp
  | succ n ih => grw [pow_succ, Nat.succ_mul, Polynomial.natDegree_mul_le, ih]

