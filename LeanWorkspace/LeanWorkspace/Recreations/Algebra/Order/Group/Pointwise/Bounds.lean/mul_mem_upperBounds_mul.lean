import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem mul_mem_upperBounds_mul (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    a * b ∈ upperBounds (s * t) := forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

