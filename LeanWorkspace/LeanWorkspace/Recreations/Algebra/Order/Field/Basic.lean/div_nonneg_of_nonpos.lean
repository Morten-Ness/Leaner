import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b := div_eq_mul_inv a b ▸ mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos'.2 hb)

