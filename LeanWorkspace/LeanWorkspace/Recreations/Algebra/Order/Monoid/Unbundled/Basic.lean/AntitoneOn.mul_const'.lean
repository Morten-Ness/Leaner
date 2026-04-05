import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem AntitoneOn.mul_const' [MulRightMono α] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => f x * a) s := mul_left_mono.comp_antitoneOn hf

