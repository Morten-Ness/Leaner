import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹ := isGLB_inv'.2 h

