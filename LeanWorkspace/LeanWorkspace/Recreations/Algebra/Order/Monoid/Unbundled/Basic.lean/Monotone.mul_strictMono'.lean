import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem Monotone.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : Monotone f)
    (hg : StrictMono g) :
    StrictMono fun x => f x * g x := fun _ _ h => mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

