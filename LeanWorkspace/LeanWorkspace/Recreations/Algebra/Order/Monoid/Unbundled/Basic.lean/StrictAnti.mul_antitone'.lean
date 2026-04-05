import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftMono α] [MulRightStrictMono α]

theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) :
    StrictAnti fun x => f x * g x := fun _ _ h => mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

