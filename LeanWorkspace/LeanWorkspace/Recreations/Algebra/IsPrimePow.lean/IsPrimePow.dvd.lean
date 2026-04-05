import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m := by
  grind [isPrimePow_nat_iff, Nat.dvd_prime_pow, Nat.pow_eq_one]

