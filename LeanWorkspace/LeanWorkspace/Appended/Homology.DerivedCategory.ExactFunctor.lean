import Mathlib

section

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem mapDerivedCategoryFactorsh_hom_app (K : CochainComplex C₁ ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
        (DerivedCategory.quotientCompQhIso C₂).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) := F.mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app K

noncomputable instance :
    Localization.Lifting DerivedCategory.Qh
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh) F.mapDerivedCategory :=
  ⟨F.mapDerivedCategoryFactorsh⟩

noncomputable instance : F.mapDerivedCategory.CommShift ℤ :=
  CategoryTheory.Functor.commShiftOfLocalization DerivedCategory.Qh
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) ℤ
    (F.mapHomotopyCategory _ ⋙ DerivedCategory.Qh)
    F.mapDerivedCategory

end
