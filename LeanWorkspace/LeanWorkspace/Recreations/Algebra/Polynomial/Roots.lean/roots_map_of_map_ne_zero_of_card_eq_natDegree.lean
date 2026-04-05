import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem roots_map_of_map_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    (f : A →+* B) (h : p.map f ≠ 0) (hroots : p.roots.card = p.natDegree) :
    p.roots.map f = (p.map f).roots := eq_of_le_of_card_le (Polynomial.map_roots_le h) <| by
    simpa only [Multiset.card_map, hroots] using Polynomial.card_roots_map_le_natDegree p

