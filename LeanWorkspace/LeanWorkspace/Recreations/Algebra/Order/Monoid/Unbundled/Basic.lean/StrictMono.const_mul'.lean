import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftStrictMono α]

theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x := fun _ _ ab => mul_lt_mul_right (hf ab) c

