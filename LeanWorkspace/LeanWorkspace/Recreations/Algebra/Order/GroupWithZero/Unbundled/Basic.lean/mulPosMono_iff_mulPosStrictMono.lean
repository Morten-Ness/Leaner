import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] :
    MulPosMono α ↔ MulPosStrictMono α := ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

