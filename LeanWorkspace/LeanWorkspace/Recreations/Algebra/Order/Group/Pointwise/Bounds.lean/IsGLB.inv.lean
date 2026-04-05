import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹ := isLUB_inv'.2 h

