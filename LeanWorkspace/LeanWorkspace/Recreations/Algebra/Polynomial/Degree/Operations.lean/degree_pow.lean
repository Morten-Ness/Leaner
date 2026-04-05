import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem degree_pow [Nontrivial R] (p : R[X]) (n : ℕ) : degree (p ^ n) = n • degree p := map_pow (@Polynomial.degreeMonoidHom R _ _ _) _ _

