import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem coeff_expand_mul {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (Polynomial.expand R p f).coeff (n * p) = f.coeff n := by
  rw [Polynomial.coeff_expand hp, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hp]

