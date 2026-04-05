import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

variable [ZeroLEOneClass M₀]

theorem pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) := strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

