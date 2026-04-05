import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

variable [MulLeftMono α] [MulRightStrictMono α]

theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun _ hx _ hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

