import Mathlib

variable {ι M M₀ : Type*}

theorem prod_ne_zero_of_prime [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀]
    (s : Multiset M₀) (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

