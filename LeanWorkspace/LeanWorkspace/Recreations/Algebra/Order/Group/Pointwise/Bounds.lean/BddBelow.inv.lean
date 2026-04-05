import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ := bddAbove_inv.2 h

