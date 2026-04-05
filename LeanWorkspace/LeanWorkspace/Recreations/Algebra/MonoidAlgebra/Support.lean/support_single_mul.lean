import Mathlib

open scoped Pointwise

variable {k : Type u₁} {G : Type u₂} [Semiring k]

variable [Mul G]

theorem support_single_mul [IsLeftCancelMul G] (f : k[G]) (r : k)
    (hr : ∀ y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : k[G]).support = f.support.map (mulLeftEmbedding x) := by
  classical
    ext
    simp only [MonoidAlgebra.support_single_mul_eq_image f hr (IsLeftRegular.all x), mem_image,
      mem_map, mulLeftEmbedding_apply]

