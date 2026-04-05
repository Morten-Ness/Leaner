import Mathlib

variable {R S : Type*}

variable [Semiring R] {x y : R} (p n : ℕ)

variable [hR : ExpChar R p]

theorem add_pow_expChar_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by
  obtain _ | hprime := hR
  · simp only [pow_one]
  · let ⟨r, hr⟩ := exists_add_pow_prime_eq h hprime
    simp [hr]

