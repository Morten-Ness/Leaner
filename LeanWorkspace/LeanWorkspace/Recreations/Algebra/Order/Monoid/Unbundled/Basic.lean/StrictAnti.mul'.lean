import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem StrictAnti.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictAnti f) (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x := fun _ _ ab => mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

