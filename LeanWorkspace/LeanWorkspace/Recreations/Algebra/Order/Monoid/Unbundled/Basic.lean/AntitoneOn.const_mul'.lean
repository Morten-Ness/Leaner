import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem AntitoneOn.const_mul' [MulLeftMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := mul_right_mono.comp_antitoneOn hf

