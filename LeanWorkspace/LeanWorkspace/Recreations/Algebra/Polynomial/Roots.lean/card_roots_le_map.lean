import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_card (Polynomial.map_roots_le h)

