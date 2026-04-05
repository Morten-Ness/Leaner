import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 := left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nonzero M₀`.

