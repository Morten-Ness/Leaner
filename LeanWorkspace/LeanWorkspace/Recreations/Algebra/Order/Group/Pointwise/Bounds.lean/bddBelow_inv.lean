import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s := (OrderIso.inv G).bddBelow_preimage

