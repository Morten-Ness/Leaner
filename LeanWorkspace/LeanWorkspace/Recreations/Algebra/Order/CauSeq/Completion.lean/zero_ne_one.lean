import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem zero_ne_one : (0 : (CauSeq.Completion.Cauchy abv)) ≠ 1 := fun h => CauSeq.Completion.cau_seq_zero_ne_one <| CauSeq.Completion.mk_eq.1 h

