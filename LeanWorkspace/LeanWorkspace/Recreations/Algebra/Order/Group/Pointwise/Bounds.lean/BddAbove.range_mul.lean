import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

theorem BddAbove.range_mul (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g)) :
    BddAbove (Set.range fun i ↦ f i * g i) := .range_comp (f := fun i ↦ (f i, g i)) (bddAbove_range_prod.2 ⟨hf, hg⟩)
    (monotone_fst.mul' monotone_snd)

