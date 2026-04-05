import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b where
  mp h := div_mul_cancel₀ b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le
  mpr h := calc
    a = a * c * (1 / c) := mul_mul_div a (ne_of_lt hc)
    _ ≥ b * (1 / c) := mul_le_mul_of_nonpos_right h <| inv_eq_one_div c ▸ (inv_lt_zero'.2 hc).le
    _ = b / c := (div_eq_mul_one_div b c).symm

