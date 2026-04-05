import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] :
    MulPosReflectLE α ↔ MulPosReflectLT α := ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

