import Mathlib

variable {R S : Type*}

variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

theorem Nat.Prime.dvd_add_pow_sub_pow_of_dvd (hpri : p.Prime) {r : R} (h₁ : r ∣ x ^ p)
    (h₂ : r ∣ p * x) : r ∣ (x + y) ^ p - y ^ p := by
  rw [add_pow_prime_eq hpri, add_right_comm, add_assoc, add_sub_assoc, add_sub_cancel_right]
  exact dvd_add h₁ (h₂.trans <| (dvd_mul_right ..).trans <| dvd_mul_right ..)

