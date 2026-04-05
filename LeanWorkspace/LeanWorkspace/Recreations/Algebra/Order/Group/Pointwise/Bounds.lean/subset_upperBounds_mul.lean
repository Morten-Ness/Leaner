import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem subset_upperBounds_mul (s t : Set M) : upperBounds s * upperBounds t ⊆ upperBounds (s * t) := image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

