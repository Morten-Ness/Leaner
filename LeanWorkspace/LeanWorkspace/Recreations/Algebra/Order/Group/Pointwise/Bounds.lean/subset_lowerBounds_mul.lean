import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem subset_lowerBounds_mul (s t : Set M) : lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) := subset_upperBounds_mul (M := Mᵒᵈ) _ _

