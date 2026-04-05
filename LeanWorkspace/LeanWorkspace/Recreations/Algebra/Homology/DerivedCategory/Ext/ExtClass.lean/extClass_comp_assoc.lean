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


theorem extClass_comp_assoc {Y : C} {n : ℕ} (γ : Ext S.X₂ Y n) {n' : ℕ} {h : 1 + n = n'} :
    hS.extClass.comp ((Ext.mk₀ S.f).comp γ (zero_add n)) h = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia),
    CategoryTheory.ShortComplex.ShortExact.extClass_comp, Ext.zero_comp]

