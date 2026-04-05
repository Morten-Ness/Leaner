import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

theorem ofRat_sub (x y : β) : CauSeq.Completion.ofRat (x - y) = (CauSeq.Completion.ofRat x - CauSeq.Completion.ofRat y : CauSeq.Completion.Cauchy abv) := congr_arg CauSeq.Completion.mk (const_sub _ _)

noncomputable instance CauSeq.Completion.Cauchy.instNonTrivial [Nontrivial β] : Nontrivial (CauSeq.Completion.Cauchy abv) :=
  CauSeq.Completion.ofRat_injective.nontrivial

