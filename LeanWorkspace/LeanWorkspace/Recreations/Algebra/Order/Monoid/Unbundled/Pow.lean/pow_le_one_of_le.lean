import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M}

theorem pow_le_one_of_le (ha : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := Left.one_le_pow_of_le (M := Mᵒᵈ) ha n

