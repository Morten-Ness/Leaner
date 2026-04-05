import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree p := calc
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree (p - C a) :=
      Polynomial.card_roots <| mt sub_eq_zero.1 fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

