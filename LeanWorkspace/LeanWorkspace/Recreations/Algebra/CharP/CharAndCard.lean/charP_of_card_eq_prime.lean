import Mathlib

theorem charP_of_card_eq_prime {R : Type*} [NonAssocRing R] [Fintype R] {p : ℕ} [hp : Fact p.Prime]
    (hR : Fintype.card R = p) : CharP R p := have := Fintype.one_lt_card_iff_nontrivial.1 (hR ▸ hp.1.one_lt)
  (CharP.charP_iff_prime_eq_zero hp.1).2 (hR ▸ Nat.cast_card_eq_zero R)

