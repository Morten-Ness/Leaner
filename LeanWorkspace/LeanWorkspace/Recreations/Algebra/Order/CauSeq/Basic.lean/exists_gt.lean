import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem exists_gt (f : CauSeq α abs) : ∃ a : α, f < CauSeq.const a := let ⟨K, H⟩ := CauSeq.bounded f
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [CauSeq.sub_apply, CauSeq.const_apply, le_sub_iff_add_le', add_le_add_iff_right]
    exact le_of_lt (abs_lt.1 (H _)).2⟩

