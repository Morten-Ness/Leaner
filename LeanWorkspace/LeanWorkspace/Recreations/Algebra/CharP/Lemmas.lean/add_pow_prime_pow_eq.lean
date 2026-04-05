import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)

theorem add_pow_prime_pow_eq :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * x * y *
          ∑ k ∈ Ioo 0 (p ^ n), x ^ (k - 1) * y ^ (p ^ n - k - 1) * ↑((p ^ n).choose k / p) := (Commute.all x y).add_pow_prime_pow_eq hp n

