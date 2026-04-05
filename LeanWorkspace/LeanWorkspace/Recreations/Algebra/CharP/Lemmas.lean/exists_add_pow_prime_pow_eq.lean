import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)

theorem exists_add_pow_prime_pow_eq :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * x * y * r := Commute.exists_add_pow_prime_pow_eq (Commute.all x y) hp n

