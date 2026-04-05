import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b where
  mp h := div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_lt_mul_of_neg_right h hc
  mpr h := calc
    a = a * c * c⁻¹ := mul_inv_cancel_right₀ hc.ne _ |>.symm
    _ > b * c⁻¹ := mul_lt_mul_of_neg_right h <| inv_lt_zero'.2 hc
    _ = b / c := division_def b c |>.symm

