import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem zero_divByMonic (p : R[X]) : 0 /ₘ p = 0 := by
  grind [Polynomial.divByMonic, Polynomial.divModByMonicAux]

