import Mathlib

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)

theorem TensorProduct.spanFinrank_top_le_of_fg (fg : N.FG) :
    (⊤ : Submodule A (A ⊗[R] N)).spanFinrank ≤ N.spanFinrank := by
  grw [← Submodule.baseChange_top, ← N.spanFinrank_top, (N.fg_top.mpr fg).spanFinrank_baseChange_le]

