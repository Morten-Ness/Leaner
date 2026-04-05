import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C]

theorem Exact.shortExact {S : CategoryTheory.ShortComplex C} (hS : S.Exact) (h : S.HomologyData) :
    (CategoryTheory.ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)).ShortExact where
  exact := by
    have := hS.epi_f' h.left
    have := hS.mono_g' h.right
    let S' := CategoryTheory.ShortComplex.mk h.left.i S.g (by simp)
    let S'' := CategoryTheory.ShortComplex.mk _ _ (h.exact_iff_i_p_zero.1 hS)
    let a : S ⟶ S' :=
      { τ₁ := h.left.f'
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _ }
    let b : S'' ⟶ S' :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := h.right.g' }
    rwa [CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono b,
      ← CategoryTheory.ShortComplex.exact_iff_of_epi_of_isIso_of_mono a]

