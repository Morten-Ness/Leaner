import Mathlib

variable {R S : Type*}

variable [CommSemiring R] (x y : R) (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem add_pow_eq_mul_pow_add_pow_div_char :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) := add_pow_eq_mul_pow_add_pow_div_expChar ..

