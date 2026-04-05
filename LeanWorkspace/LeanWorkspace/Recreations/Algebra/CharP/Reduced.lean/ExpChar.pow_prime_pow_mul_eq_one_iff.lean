import Mathlib

variable {R : Type*} [CommRing R] [IsReduced R]

theorem ExpChar.pow_prime_pow_mul_eq_one_iff (p k m : ℕ) [ExpChar R p] (x : R) :
    x ^ (p ^ k * m) = 1 ↔ x ^ m = 1 := by
  rw [pow_mul']
  convert ← (iterateFrobenius_inj R p k).eq_iff
  apply map_one

