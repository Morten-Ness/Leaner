import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftStrictMono α]

theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) :
    StrictMonoOn (fun x => c * f x) s := fun _ ha _ hb ab => mul_lt_mul_right (hf ha hb ab) c

