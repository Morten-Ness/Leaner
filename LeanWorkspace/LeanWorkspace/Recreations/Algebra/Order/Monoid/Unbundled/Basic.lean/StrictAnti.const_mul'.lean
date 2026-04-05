import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftStrictMono α]

theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x := fun _ _ ab => mul_lt_mul_right (hf ab) c

