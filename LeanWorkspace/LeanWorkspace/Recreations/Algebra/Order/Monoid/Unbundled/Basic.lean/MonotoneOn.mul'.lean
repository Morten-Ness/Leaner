import Mathlib

variable {α β : Type*}

variable [Mul α] [Preorder α] [Preorder β] {f g : β → α} {s : Set β}

theorem MonotoneOn.mul' [MulLeftMono α]
    [MulRightMono α] (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x * g x) s := fun _ hx _ hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

