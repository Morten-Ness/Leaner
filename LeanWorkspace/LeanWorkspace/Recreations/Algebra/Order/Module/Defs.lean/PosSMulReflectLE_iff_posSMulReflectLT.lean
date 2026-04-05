import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Semiring α] [AddCommGroup β] [Module α β]

variable [IsDomain α] [Module.IsTorsionFree α β]

variable [PartialOrder α] [PartialOrder β]

theorem PosSMulReflectLE_iff_posSMulReflectLT : PosSMulReflectLE α β ↔ PosSMulReflectLT α β := ⟨fun _ ↦ inferInstance, fun _ ↦ PosSMulReflectLT.toPosSMulReflectLE⟩

