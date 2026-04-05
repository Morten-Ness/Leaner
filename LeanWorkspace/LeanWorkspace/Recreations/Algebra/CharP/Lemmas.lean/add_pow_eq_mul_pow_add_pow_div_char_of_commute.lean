import Mathlib

variable {R S : Type*}

variable [Semiring R] {x y : R} (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem add_pow_eq_mul_pow_add_pow_div_char_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) := add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ h

