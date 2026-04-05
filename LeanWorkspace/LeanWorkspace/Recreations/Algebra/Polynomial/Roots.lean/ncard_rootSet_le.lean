import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ncard_rootSet_le (p : A[X]) (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] :
    Set.ncard (p.rootSet B) ≤ p.natDegree := by
  classical
  grw [Polynomial.rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact Polynomial.card_roots_map_le_natDegree p

