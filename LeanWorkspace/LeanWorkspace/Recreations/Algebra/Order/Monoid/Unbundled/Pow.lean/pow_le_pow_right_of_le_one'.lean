import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M} {n : ℕ}

theorem pow_le_pow_right_of_le_one' {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n := pow_le_pow_right' (M := Mᵒᵈ) ha h

