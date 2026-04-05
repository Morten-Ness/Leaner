import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem ofNat_eq_zero [p.AtLeastTwo] : (ofNat(p) : R) = 0 := cast_eq_zero R p

