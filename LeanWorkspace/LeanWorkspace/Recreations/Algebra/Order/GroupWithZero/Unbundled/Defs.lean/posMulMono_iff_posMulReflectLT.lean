import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α := ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩

