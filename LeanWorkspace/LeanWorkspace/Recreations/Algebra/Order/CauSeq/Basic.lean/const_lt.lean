import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem const_lt {x y : α} : CauSeq.const x < CauSeq.const y ↔ x < y := show CauSeq.Pos _ ↔ _ by rw [← CauSeq.const_sub, CauSeq.const_pos, sub_pos]

