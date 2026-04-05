import Mathlib

variable {ι M M₀ R : Type*}

variable [CommMonoidWithZero M₀] {s : Multiset M₀}

variable [NoZeroDivisors M₀] [Nontrivial M₀] {s : Multiset M₀}

theorem prod_ne_zero (h : (0 : M₀) ∉ s) : s.prod ≠ 0 := mt prod_eq_zero_iff.1 h

