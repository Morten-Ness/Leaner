import Mathlib

variable {R S : Type*}

variable [CommSemiring R] (x y : R) (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem add_pow_char : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar ..

