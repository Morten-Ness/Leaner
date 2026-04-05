import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem degree_erase_lt (hp : p ≠ 0) : Polynomial.degree (p.erase (Polynomial.natDegree p)) < Polynomial.degree p := by
  apply lt_of_le_of_ne (Polynomial.degree_erase_le _ _)
  rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree, support_erase]
  exact fun h => Finset.notMem_erase _ _ (mem_of_max h)

