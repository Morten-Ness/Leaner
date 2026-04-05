import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingCoeff_eq_zero : Polynomial.trailingCoeff p = 0 ↔ p = 0 := ⟨fun h =>
    _root_.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h)
        (mem_of_min (Polynomial.trailingDegree_eq_natTrailingDegree hp)),
    fun h => h.symm ▸ leadingCoeff_zero⟩

