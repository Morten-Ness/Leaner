import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    #Z ≤ p.natDegree := (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

