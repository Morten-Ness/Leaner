import Mathlib

variable {M : Type*}

variable [Monoid M] [Subsingleton Mˣ]

theorem prime_dvd_prime_iff_eq {M : Type*} [CommMonoidWithZero M] [IsCancelMulZero M]
    [Subsingleton Mˣ] {p q : M} (pp : Prime p) (qp : Prime q) : p ∣ q ↔ p = q := by
  rw [pp.dvd_prime_iff_associated qp, ← associated_eq_eq]

