import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Antitone.const_mul' [MulLeftMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ a * f x := mul_right_mono.comp_antitone hf

