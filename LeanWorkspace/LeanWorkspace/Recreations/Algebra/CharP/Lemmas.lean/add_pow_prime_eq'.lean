import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)

theorem add_pow_prime_eq' :
    (x + y) ^ p = x ^ p + y ^ p + p * ∑ k ∈ Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) := (Commute.all x y).add_pow_prime_eq' hp

