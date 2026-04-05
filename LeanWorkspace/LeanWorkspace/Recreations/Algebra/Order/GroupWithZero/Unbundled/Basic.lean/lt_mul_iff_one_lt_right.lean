import Mathlib

variable {α M₀ G₀ : Type*}

variable [MulOneClass α] [Zero α] {a b c d : α}

variable [Preorder α]

theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b := Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

