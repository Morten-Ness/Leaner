import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)

theorem add_pow_prime_eq :
    (x + y) ^ p =
      x ^ p + y ^ p + p * x * y *
        ∑ k ∈ Ioo 0 p, x ^ (k - 1) * y ^ (p - k - 1) * ↑(p.choose k / p) := (Commute.all x y).add_pow_prime_eq hp

