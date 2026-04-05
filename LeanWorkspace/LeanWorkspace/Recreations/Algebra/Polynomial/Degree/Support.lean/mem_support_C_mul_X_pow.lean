import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mem_support_C_mul_X_pow {n a : ℕ} {c : R} (h : a ∈ support (Polynomial.C c * Polynomial.X ^ n)) : a = n := mem_singleton.1 <| support_C_mul_X_pow' n c h

