import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem lim_add (f g : CauSeq β abv) : CauSeq.lim f + CauSeq.lim g = CauSeq.lim (f + g) := CauSeq.eq_lim_of_const_equiv <|
    show LimZero (const abv (CauSeq.lim f + CauSeq.lim g) - (f + g)) by
      rw [const_add, add_sub_add_comm]
      exact add_limZero (Setoid.symm (CauSeq.equiv_lim f)) (Setoid.symm (CauSeq.equiv_lim g))

