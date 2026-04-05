import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem BddBelow.mul (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) := (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

