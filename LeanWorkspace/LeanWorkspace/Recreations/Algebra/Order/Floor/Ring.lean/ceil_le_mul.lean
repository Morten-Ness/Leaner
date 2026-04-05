import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b ≤ a) : ⌈a⌉ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [Int.ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (Int.ceil_lt_mul hb hba).le

