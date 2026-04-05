import Mathlib

theorem not_isUnit_prime_of_dvd_card {R : Type*} [CommRing R] [Fintype R] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Fintype.card R) : ¬IsUnit (p : R) := mt (isUnit_iff_not_dvd_char R p).mp
    (Classical.not_not.mpr ((prime_dvd_char_iff_dvd_card p).mpr hp))

