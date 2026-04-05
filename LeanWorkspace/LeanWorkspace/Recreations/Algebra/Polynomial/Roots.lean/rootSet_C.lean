import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).rootSet S = ∅ := by
  classical
  rw [Polynomial.rootSet_def, Polynomial.aroots_C, Multiset.toFinset_zero, Finset.coe_empty]

