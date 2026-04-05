import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable {k : Type*} [Field k] [LinearOrder k] [IsStrictOrderedRing k] [FloorRing k] {a b : k}

theorem ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a) : ⌈a⌉ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ ≤ (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := Int.ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

