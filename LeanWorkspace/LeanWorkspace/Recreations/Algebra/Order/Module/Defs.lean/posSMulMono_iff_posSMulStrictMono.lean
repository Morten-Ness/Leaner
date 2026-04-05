import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Semiring α] [AddCommGroup β] [Module α β]

variable [IsDomain α] [Module.IsTorsionFree α β]

variable [PartialOrder α] [PartialOrder β]

theorem posSMulMono_iff_posSMulStrictMono : PosSMulMono α β ↔ PosSMulStrictMono α β := ⟨fun _ ↦ PosSMulMono.toPosSMulStrictMono, fun _ ↦ inferInstance⟩

