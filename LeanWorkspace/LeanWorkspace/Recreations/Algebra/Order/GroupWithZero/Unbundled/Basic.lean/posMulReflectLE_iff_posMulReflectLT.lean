import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [MonoidWithZero α]

variable [PartialOrder α]

theorem posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] :
    PosMulReflectLE α ↔ PosMulReflectLT α := ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

