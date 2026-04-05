import Mathlib

variable {R S : Type*}

variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

variable [hp : Fact p.Prime] [CharP R p]

theorem sub_pow_eq_mul_pow_sub_pow_div_char :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) := sub_pow_eq_mul_pow_sub_pow_div_expChar ..

