import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem modByMonic_add_div (p q : R[X]) : p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (Polynomial.modByMonic_eq_sub_mul_div p q)

