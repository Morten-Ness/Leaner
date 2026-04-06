FAIL
import Mathlib

variable (R : Type*) [CommRing R]

theorem reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  constructor
  · intro h p hp hmc
    exact h p hp.pos hmc
  · intro h p hp hmc
    have hprime : p.Prime := by
      exact Nat.prime_of_mixedCharZero hmc
    exact h p hprime hmc
