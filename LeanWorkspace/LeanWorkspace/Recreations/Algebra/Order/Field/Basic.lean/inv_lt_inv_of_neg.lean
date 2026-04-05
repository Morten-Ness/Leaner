import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a := by
  have := div_lt_iff_of_neg ha (b := 1) (a := b⁻¹)
  rwa [one_div, mul_comm b⁻¹, ← division_def, div_lt_iff_of_neg hb, one_mul] at this

