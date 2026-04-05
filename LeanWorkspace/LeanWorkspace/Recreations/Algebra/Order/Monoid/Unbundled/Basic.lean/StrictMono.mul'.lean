import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem StrictMono.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun _ _ ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

