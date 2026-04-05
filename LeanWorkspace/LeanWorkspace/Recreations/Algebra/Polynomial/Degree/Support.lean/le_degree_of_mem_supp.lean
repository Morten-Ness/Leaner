import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem le_degree_of_mem_supp (a : ℕ) : a ∈ p.support → ↑a ≤ degree p := le_degree_of_ne_zero ∘ mem_support_iff.mp

