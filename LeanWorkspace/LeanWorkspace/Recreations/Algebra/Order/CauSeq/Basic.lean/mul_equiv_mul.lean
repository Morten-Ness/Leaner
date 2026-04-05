import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 * g1 ≈ f2 * g2 := by
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel]
    using CauSeq.add_limZero (CauSeq.mul_limZero_left g1 hf) (CauSeq.mul_limZero_right f2 hg)

