import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem BddBelow.range_inv {α : Type*} {f : α → G} (hf : BddBelow (Set.range f)) :
    BddAbove (Set.range (fun x => (f x)⁻¹)) := hf.range_comp (OrderIso.inv G).monotone

