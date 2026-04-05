import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem zero_isRoot_iff_coeff_zero_eq_zero {p : R[X]} : IsRoot p 0 ↔ p.coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, IsRoot]

alias ⟨coeff_zero_eq_zero_of_zero_isRoot, zero_isRoot_of_coeff_zero_eq_zero⟩ :=
  zero_isRoot_iff_coeff_zero_eq_zero

