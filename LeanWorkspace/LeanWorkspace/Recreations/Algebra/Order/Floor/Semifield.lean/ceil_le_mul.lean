import Mathlib

variable {R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K] {a b : K}

theorem ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b ≤ a) : ⌈a⌉₊ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (Nat.ceil_lt_mul hb hba).le

