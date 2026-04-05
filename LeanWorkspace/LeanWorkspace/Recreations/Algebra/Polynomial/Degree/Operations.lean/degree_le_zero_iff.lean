import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_le_zero_iff : degree p ≤ 0 ↔ p = Polynomial.C (coeff p 0) := ⟨Polynomial.eq_C_of_degree_le_zero, fun h => h.symm ▸ degree_C_le⟩

