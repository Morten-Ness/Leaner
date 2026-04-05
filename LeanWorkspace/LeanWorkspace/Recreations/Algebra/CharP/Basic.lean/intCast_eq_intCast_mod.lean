import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) := (CharP.intCast_eq_intCast R p).mpr (Int.mod_modEq a p).symm

