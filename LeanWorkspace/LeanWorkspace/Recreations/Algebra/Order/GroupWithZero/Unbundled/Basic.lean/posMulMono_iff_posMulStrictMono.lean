import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] :
    PosMulMono α ↔ PosMulStrictMono α := ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

