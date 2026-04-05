import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem supp_subset_range_natDegree_succ : p.support ⊆ Finset.range (natDegree p + 1) := Polynomial.supp_subset_range (Nat.lt_succ_self _)

