import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem mul_mem_lowerBounds_mul (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    a * b ∈ lowerBounds (s * t) := mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

