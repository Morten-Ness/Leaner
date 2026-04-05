import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem coeff_expand_mul' {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (Polynomial.expand R p f).coeff (p * n) = f.coeff n := by rw [mul_comm, Polynomial.coeff_expand_mul hp]

