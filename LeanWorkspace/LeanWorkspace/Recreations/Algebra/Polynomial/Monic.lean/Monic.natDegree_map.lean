import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R]

theorem Monic.natDegree_map [Semiring S] [Nontrivial S] {P : R[X]} (hmo : P.Monic) (f : R →+* S) :
    (P.map f).natDegree = P.natDegree := by
  refine le_antisymm natDegree_map_le (le_natDegree_of_ne_zero ?_)
  rw [coeff_map, Polynomial.Monic.coeff_natDegree hmo, map_one]
  exact one_ne_zero

