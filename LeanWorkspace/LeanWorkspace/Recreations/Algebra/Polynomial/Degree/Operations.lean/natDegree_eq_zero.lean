import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_eq_zero {p : R[X]} : p.natDegree = 0 ↔ ∃ x, Polynomial.C x = p := ⟨fun h ↦ ⟨_, (Polynomial.eq_C_of_natDegree_eq_zero h).symm⟩, by aesop⟩

