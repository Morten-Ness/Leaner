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


theorem extClass_naturality {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    h₁.extClass.comp (Ext.mk₀ f.τ₁) (add_zero 1) =
      (Ext.mk₀ f.τ₃).comp h₂.extClass (zero_add 1) := by
  letI := HasDerivedCategory.standard C
  ext
  simpa [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using (singleTriangle.map h₁ h₂ f).comm₃

