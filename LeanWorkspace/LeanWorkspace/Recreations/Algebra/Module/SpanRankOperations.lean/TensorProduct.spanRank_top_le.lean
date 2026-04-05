import Mathlib

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

theorem TensorProduct.spanRank_top_le : (⊤ : Submodule A (A ⊗[R] N)).spanRank ≤ N.spanRank.lift := by
  grw [← Submodule.baseChange_top, ← N.spanRank_top, spanRank_baseChange_le]

