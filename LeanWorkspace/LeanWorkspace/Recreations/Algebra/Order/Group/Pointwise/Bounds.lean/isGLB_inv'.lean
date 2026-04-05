import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a := (OrderIso.inv G).isGLB_preimage'

