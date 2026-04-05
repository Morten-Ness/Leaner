import Mathlib

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_add (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n := PNatPowAssoc.ppow_add k n x

