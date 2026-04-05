import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem ofRat_div (x y : β) : CauSeq.Completion.ofRat (x / y) = (CauSeq.Completion.ofRat x / CauSeq.Completion.ofRat y : CauSeq.Completion.Cauchy abv) := by
  simp only [div_eq_mul_inv, CauSeq.Completion.ofRat_inv, CauSeq.Completion.ofRat_mul]

