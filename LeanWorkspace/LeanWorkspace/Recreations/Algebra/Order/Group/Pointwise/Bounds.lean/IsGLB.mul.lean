import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem IsGLB.mul (hs : IsGLB s a) (ht : IsGLB t b) :
    IsGLB (s * t) (a * b) := IsLUB.mul (G := Gᵒᵈ) hs ht

