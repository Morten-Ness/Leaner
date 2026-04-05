import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_eq_of_degree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.degree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val := by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx ↦ (Polynomial.mem_roots p hp).mpr (hS x hx)))
  · simpa using (Polynomial.card_roots p hp).trans hcard

