import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Antitone.mul_const' [MulRightMono α] (hf : Antitone f) (a : α) : Antitone fun x ↦ f x * a := mul_left_mono.comp_antitone hf

