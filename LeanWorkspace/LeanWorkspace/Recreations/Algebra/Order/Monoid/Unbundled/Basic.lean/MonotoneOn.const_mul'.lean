import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem MonotoneOn.const_mul' [MulLeftMono α] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := mul_right_mono.comp_monotoneOn hf

