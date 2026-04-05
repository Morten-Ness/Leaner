import Mathlib

variable {R S : Type*}

variable [Semiring R] {x y : R} (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem add_pow_char_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar_of_commute _ h

