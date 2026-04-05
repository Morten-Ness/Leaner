import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem MonotoneOn.mul_strictMono' [MulLeftStrictMono α]
    [MulRightMono α] {f g : β → α} (hf : MonotoneOn f s)
    (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s := fun _ hx _ hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

