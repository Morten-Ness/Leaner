import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := fun h ↦
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero (1 : CauSeq _ abv) := by simpa
  one_ne_zero <| const_limZero.1 this

