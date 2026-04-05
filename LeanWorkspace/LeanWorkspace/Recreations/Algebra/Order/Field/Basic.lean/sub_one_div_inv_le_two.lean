import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem sub_one_div_inv_le_two (a2 : 2 ≤ a) : (1 - 1 / a)⁻¹ ≤ 2 := by
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_anti₀ (inv_pos.2 <| zero_lt_two' α) ?_).trans_eq (inv_inv (2 : α))
  -- move `1 / a` to the left and `2⁻¹` to the right.
  rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
  -- take inverses on both sides and use the assumption `2 ≤ a`.
  convert (one_div a).le.trans (inv_anti₀ zero_lt_two a2) using 1
  -- show `1 - 1 / 2 = 1 / 2`.
  rw [sub_eq_iff_eq_add, ← two_mul, mul_inv_cancel₀ two_ne_zero]

