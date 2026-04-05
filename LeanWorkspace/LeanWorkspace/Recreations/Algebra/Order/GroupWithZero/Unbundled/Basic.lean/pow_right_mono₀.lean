import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 ≤ a) : Monotone (a ^ ·) := monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

