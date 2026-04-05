import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem hasSmallLocalizedShiftedHom_of_isLE_of_isGE
    [CategoryTheory.HasExt.{w} C] (K L : CochainComplex C ℤ)
    (a b : ℤ) [K.IsGE a] [K.IsLE a] [L.IsGE b] [L.IsLE b] :
    HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) ℤ K L := by
  letI := HasDerivedCategory.standard
  obtain ⟨X, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj K) a
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE (Q.obj L) b
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  exact fun p q ↦ small_of_injective (f := fun φ ↦
    ((singleFunctors C).shiftIso p (a - p) a (by simp)).inv.app X ≫
      eX.inv⟦p⟧' ≫ φ ≫ eY.hom⟦q⟧' ≫
        ((singleFunctors C).shiftIso q (b - q) b (by simp)).hom.app Y)
    (fun φ₁ φ₂ h ↦ by simpa [cancel_epi, cancel_mono] using h)

