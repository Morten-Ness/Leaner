import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a := (OrderIso.inv G).isLUB_preimage'

