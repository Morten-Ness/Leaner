import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 := div_eq_mul_inv a b ▸ mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

