import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)

theorem exists_add_pow_prime_eq : ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * x * y * r := Commute.exists_add_pow_prime_eq (Commute.all x y) hp

