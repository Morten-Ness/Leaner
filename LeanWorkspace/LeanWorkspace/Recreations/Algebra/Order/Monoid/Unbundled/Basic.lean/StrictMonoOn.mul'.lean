import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem StrictMonoOn.mul' [MulLeftStrictMono α]
    [MulRightStrictMono α] (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun _ ha _ hb ab => mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

