import Mathlib

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_one (x : M) : x ^ (1 : ℕ+) = x := PNatPowAssoc.ppow_one x

