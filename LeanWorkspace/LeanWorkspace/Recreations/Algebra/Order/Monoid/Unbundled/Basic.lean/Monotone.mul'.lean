import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Monotone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

