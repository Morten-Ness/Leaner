import Mathlib

variable {ι κ M M₀ R : Type*}

variable [MonoidWithZero M₀] {l : List M₀}

variable [Nontrivial M₀] [NoZeroDivisors M₀]

theorem prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod ≠ 0 := mt prod_eq_zero_iff.1 hL

