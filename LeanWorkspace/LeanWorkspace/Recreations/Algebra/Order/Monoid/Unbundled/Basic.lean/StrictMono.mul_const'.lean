import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulRightStrictMono α]

theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c := fun _ _ ab => mul_lt_mul_left (hf ab) c

