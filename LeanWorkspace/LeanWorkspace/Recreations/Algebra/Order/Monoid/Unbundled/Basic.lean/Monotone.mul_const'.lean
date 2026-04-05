import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Monotone.mul_const' [MulRightMono α] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := mul_left_mono.comp hf

