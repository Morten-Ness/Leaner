import Mathlib

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (Polynomial.expand R n) := fun g g' H =>
  ext fun k => by rw [← Polynomial.coeff_expand_mul hn, H, Polynomial.coeff_expand_mul hn]

