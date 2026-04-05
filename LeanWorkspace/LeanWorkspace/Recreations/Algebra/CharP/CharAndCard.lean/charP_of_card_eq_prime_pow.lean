import Mathlib

theorem charP_of_card_eq_prime_pow {R : Type*} [CommRing R] [IsDomain R] [Fintype R] {p f : ℕ}
    [hp : Fact p.Prime] (hR : Fintype.card R = p ^ f) : CharP R p := have hf : f ≠ 0 := fun h0 ↦ not_subsingleton R <|
    Fintype.card_le_one_iff_subsingleton.mp <| by simpa [h0] using hR.le
  (CharP.charP_iff_prime_eq_zero hp.out).mpr
    (by simpa [hf, hR] using Nat.cast_card_eq_zero R)

