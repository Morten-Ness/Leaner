import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_mul_single [IsRightCancelMul G] (f : k[G]) (r : k)
    (hr : ∀ y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
    ext
    simp only [MonoidAlgebra.support_mul_single_eq_image f hr (IsRightRegular.all x),
      mem_image, mem_map, mulRightEmbedding_apply]

