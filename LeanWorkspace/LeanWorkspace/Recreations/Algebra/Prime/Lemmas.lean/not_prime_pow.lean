import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

variable {a p : M}

theorem not_prime_pow {n : ℕ} (hn : n ≠ 1) : ¬Prime (a ^ n) := fun hp =>
  not_irreducible_pow hn hp.irreducible

