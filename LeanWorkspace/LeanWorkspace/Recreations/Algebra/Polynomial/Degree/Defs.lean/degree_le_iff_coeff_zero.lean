import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_le_iff_coeff_zero (f : R[X]) (n : WithBot ℕ) :
    Polynomial.degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 := by
  simp only [Polynomial.degree, Finset.max, Finset.sup_le_iff, mem_support_iff, Ne, ← not_le,
    not_imp_comm, Nat.cast_withBot]

