import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem support_smul [SMulZeroClass S R] (r : S) (p : R[X]) :
    support (r • p) ⊆ support p := by
  intro i hi
  rw [mem_support_iff] at hi ⊢
  contrapose! hi
  simp [hi]

