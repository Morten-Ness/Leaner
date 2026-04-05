import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

omit [IsStrictOrderedRing α] in
theorem strictMono_div_right_of_pos (ha : 0 < a) : StrictMono (· / a) := fun _b _c hbc ↦ div_lt_div_of_pos_right hbc ha

