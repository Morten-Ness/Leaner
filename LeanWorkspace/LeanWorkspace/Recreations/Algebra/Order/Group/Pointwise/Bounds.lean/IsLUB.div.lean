import Mathlib

open scoped Pointwise

variable {ι G M : Type*}

variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s t : Set G} {a b : G}

theorem IsLUB.div (hs : IsLUB s a) (ht : IsGLB t b) :
    IsLUB (s / t) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hs.mul ht.inv

