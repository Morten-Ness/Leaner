import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem Monic.roots_map_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic)
    (f : A →+* B) (hroots : p.roots.card = p.natDegree) : p.roots.map f = (p.map f).roots := Polynomial.roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

