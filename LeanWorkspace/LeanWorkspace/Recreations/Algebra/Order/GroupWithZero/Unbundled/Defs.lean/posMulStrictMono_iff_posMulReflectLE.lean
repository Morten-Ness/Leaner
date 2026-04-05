import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α := ⟨@PosMulStrictMono.toPosMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩

