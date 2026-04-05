import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem BddAbove.range_inv {α : Type*} {f : α → G} (hf : BddAbove (Set.range f)) :
    BddBelow (Set.range (fun x => (f x)⁻¹)) := BddBelow.range_inv (G := Gᵒᵈ) hf

