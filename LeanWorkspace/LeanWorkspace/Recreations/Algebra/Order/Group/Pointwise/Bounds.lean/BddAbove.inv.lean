import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ := bddBelow_inv.2 h

