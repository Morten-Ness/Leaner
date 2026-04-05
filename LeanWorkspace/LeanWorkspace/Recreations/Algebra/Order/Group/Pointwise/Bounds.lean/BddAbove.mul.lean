import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem BddAbove.mul (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) := (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

