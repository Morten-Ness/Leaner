import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem neg_one_pow_char_pow : (-1 : R) ^ p ^ n = -1 := neg_one_pow_expChar_pow ..

