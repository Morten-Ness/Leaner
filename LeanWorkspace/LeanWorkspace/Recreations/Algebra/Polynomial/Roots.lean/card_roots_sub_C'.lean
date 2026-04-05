import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots ≤ natDegree p := WithBot.coe_le_coe.1
    (le_trans (Polynomial.card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

