import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s := (OrderIso.inv G).bddAbove_preimage

