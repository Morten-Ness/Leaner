import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingDegree_eq_top : Polynomial.trailingDegree p = ⊤ ↔ p = 0 := ⟨fun h => support_eq_empty.1 (Finset.min_eq_top.1 h), fun h => by simp [h]⟩

