import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable (S : ShortComplex C)

variable (hS : S.ShortExact)

set_option backward.privateInPublic true in
include hS in
private theorem hasSmallLocalizedHom_S'_X₃_K :
    HasSmallLocalizedHom.{w} W (S').X₃ K := by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := ℤ)


set_option backward.privateInPublic true in
include hS in
private theorem hasSmallLocalizedShiftedHom_K_S'_X₁ :
    HasSmallLocalizedShiftedHom.{w} W ℤ K (S').X₁ := by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W ℤ qis hqis (S').X₁]
  infer_instance


theorem comp_extClass : (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0 := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, CategoryTheory.ShortComplex.ShortExact.extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

