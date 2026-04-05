import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem inv_zero : (0 : (CauSeq.Completion.Cauchy abv))⁻¹ = 0 := congr_arg CauSeq.Completion.mk <| by rw [dif_pos] <;> [rfl; exact zero_limZero]

