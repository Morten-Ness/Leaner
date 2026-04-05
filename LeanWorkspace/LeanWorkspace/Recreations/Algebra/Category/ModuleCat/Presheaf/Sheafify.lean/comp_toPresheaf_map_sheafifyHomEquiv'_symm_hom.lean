import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

variable [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom {F : PresheafOfModules.{v} R.obj}
    (hF : Presheaf.IsSheaf J F.presheaf) (f : M₀ ⟶ (restrictScalars α).obj F) :
    φ ≫ (toPresheaf R.obj).map ((PresheafOfModules.sheafifyHomEquiv' α φ hF).symm f) = (toPresheaf R₀).map f := (toPresheaf _).congr_map ((PresheafOfModules.sheafifyHomEquiv' α φ hF).apply_symm_apply f)

