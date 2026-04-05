import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem neg_one_pow_char : (-1 : R) ^ p = -1 := neg_one_pow_expChar ..

