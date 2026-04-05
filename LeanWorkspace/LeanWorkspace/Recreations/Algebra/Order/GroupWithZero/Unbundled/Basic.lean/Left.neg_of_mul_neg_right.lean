import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulZeroClass α] {a b c d : α}

variable [LinearOrder α]

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 := lt_of_not_ge fun b0 : b ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

