import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem MonotoneOn.mul_const' [MulRightMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => f x * a) s := mul_left_mono.comp_monotoneOn hf

