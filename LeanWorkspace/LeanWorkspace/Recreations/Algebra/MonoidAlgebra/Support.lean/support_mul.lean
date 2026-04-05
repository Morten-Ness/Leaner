import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_mul [DecidableEq G] (a b : k[G]) : (a * b).support ⊆ a.support * b.support := by
  rw [MonoidAlgebra.mul_def]
  exact support_sum.trans <| biUnion_subset.2 fun _x hx ↦
    support_sum.trans <| biUnion_subset.2 fun _y hy ↦
      support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy

