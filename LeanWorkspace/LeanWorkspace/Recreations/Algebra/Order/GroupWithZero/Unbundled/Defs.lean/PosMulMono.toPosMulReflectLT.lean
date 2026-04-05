import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [LinearOrder α]

theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α where
  elim := (covariant_le_iff_contravariant_lt _ _ _).1
    fun a _b _c hbc ↦ mul_le_mul_of_nonneg_left hbc a.2

