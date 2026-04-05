import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem natCast_eq_natCast_mod (a : ℕ) : (a : R) = a % p := CharP.natCast_eq_natCast' R p (Nat.mod_modEq a p).symm

