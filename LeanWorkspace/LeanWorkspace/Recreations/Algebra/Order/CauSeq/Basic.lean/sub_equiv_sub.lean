import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 - g1 ≈ f2 - g2 := by simpa only [sub_eq_add_neg] using CauSeq.add_equiv_add hf (CauSeq.neg_equiv_neg hg)

