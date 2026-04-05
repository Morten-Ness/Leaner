import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_eq_zero : Polynomial.leadingCoeff p = 0 ↔ p = 0 := ⟨fun h =>
    Classical.by_contradiction fun hp =>
      mt mem_support_iff.1 (Classical.not_not.2 h) (mem_of_max (Polynomial.degree_eq_natDegree hp)),
    fun h => h.symm ▸ Polynomial.leadingCoeff_zero⟩

