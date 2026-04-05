import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Antitone.mul_strictAnti' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : Antitone f)
    (hg : StrictAnti g) :
    StrictAnti fun x => f x * g x := fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

