import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Antitone.mul' [MulLeftMono α]
    [MulRightMono α] (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x * g x := fun _ _ h => mul_le_mul' (hf h) (hg h)

