import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem IsGLB.div (hs : IsGLB s a) (ht : IsLUB t b) :
    IsGLB (s / t) (a / b) := IsLUB.div (G := Gᵒᵈ) hs ht

