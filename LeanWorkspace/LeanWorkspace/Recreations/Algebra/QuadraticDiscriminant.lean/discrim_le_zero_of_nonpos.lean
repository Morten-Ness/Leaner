import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b c : K}

theorem discrim_le_zero_of_nonpos (h : ∀ x : K, a * (x * x) + b * x + c ≤ 0) : discrim a b c ≤ 0 := discrim_neg a b c ▸ discrim_le_zero <| by simpa only [neg_mul, ← neg_add, neg_nonneg]

