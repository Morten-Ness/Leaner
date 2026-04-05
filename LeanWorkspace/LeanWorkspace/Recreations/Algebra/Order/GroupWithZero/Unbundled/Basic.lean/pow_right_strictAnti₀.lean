import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

theorem pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) := strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

