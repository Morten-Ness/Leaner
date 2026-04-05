import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem ofNat_eq_mod (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R) = (ofNat(n) % 2 : ℕ) := CharTwo.natCast_eq_mod n

example : (37 : R) = 1 := by simp

