import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulRightStrictMono α]

theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) :
    StrictAntiOn (fun x => f x * c) s := fun _ ha _ hb ab => mul_lt_mul_left (hf ha hb ab) c

