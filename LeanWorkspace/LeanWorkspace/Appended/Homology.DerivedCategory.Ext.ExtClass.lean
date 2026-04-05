import Mathlib

section

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

end

section

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


theorem comp_extClass_assoc {Y : C} {n : ℕ} (γ : Ext S.X₁ Y n) {n' : ℕ} (h : 1 + n = n') :
    (Ext.mk₀ S.g).comp (hS.extClass.comp γ h) (zero_add n') = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia),
    CategoryTheory.ShortComplex.ShortExact.comp_extClass, Ext.zero_comp]

end

section

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


theorem extClass_comp : hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := by
  letI := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, CategoryTheory.ShortComplex.ShortExact.extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

end

section

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

end

section

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


set_option backward.isDefEq.respectTransparency false in
theorem extClass_hom [HasDerivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ := by
  change SmallShiftedHom.equiv W Q hS.extClass = _
  dsimp [CategoryTheory.ShortComplex.ShortExact.extClass, SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp]
  rw [SmallHom.equiv_mkInv, SmallHom.equiv_mk]
  dsimp [singleδ, triangleOfSESδ]
  rw [Category.assoc, Category.assoc, Category.assoc,
    singleFunctorsPostcompQIso_hom_hom, singleFunctorsPostcompQIso_inv_hom,
    NatTrans.id_app, Category.id_comp, NatTrans.id_app]
  simp only [SingleFunctors.postcomp, Functor.comp_obj]
  unfold CochainComplex.singleFunctors
  rw [Functor.map_id, Category.comp_id]
  rfl

end

section

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

end
