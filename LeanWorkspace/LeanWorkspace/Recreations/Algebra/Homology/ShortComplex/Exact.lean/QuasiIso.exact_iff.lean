import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem QuasiIso.exact_iff {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [QuasiIso φ] : S₁.Exact ↔ S₂.Exact := by
  simp only [CategoryTheory.ShortComplex.exact_iff_isZero_homology]
  exact Iso.isZero_iff (asIso (homologyMap φ))

