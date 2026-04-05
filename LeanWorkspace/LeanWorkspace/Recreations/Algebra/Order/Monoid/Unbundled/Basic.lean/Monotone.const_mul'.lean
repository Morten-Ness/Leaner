import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Monotone.const_mul' [MulLeftMono α] (hf : Monotone f) (a : α) : Monotone fun x ↦ a * f x := mul_right_mono.comp hf

