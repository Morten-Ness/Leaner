import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_mk {f} (hf) : (CauSeq.Completion.mk (abv := abv) f)⁻¹ = CauSeq.Completion.mk (inv f hf) :=
  congr_arg CauSeq.Completion.mk <| by rw [dif_neg]

