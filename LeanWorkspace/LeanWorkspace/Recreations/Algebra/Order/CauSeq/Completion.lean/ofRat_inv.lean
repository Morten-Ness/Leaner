import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem ofRat_inv (x : β) : CauSeq.Completion.ofRat x⁻¹ = ((CauSeq.Completion.ofRat x)⁻¹ : (CauSeq.Completion.Cauchy abv)) := congr_arg CauSeq.Completion.mk <| by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]

noncomputable instance instDivInvMonoid : DivInvMonoid (CauSeq.Completion.Cauchy abv) where

