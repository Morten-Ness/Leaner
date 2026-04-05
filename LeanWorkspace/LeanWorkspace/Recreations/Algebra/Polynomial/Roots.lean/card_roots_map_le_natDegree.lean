import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem card_roots_map_le_natDegree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) : (p.map f).roots.card ≤ p.natDegree := Polynomial.card_roots' _ |>.trans natDegree_map_le

