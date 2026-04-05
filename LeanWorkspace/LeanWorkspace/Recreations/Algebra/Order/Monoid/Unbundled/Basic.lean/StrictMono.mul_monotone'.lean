import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftMono α] [MulRightStrictMono α]

theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) :
    StrictMono fun x => f x * g x := fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

