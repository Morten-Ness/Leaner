import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_neg (f : CauSeq β abv) : CauSeq.lim (-f) = -CauSeq.lim f := CauSeq.lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-CauSeq.lim f)) by
      rw [const_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
      exact Setoid.symm (CauSeq.equiv_lim f))

