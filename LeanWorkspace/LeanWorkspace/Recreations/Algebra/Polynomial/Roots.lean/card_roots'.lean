import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem card_roots' (p : R[X]) : Multiset.card p.roots ≤ natDegree p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (Polynomial.card_roots hp0) (le_of_eq <| degree_eq_natDegree hp0))

