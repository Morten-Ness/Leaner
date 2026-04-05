import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem BddBelow.range_mul (hf : BddBelow (Set.range f)) (hg : BddBelow (Set.range g)) :
    BddBelow (Set.range fun i ↦ f i * g i) := BddAbove.range_mul (M := Mᵒᵈ) hf hg

