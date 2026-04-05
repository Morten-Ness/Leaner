import Mathlib

variable {R S : Type*}

variable [Semiring R] {x y : R} (p n : ℕ)

variable [hR : ExpChar R p]

theorem add_pow_expChar_pow_of_commute (h : Commute x y) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  obtain _ | hprime := hR
  · simp only [one_pow, pow_one]
  · let ⟨r, hr⟩ := exists_add_pow_prime_pow_eq h hprime n
    simp [hr]

