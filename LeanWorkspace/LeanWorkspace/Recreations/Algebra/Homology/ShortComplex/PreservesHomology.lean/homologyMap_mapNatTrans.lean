import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

variable {S}
  {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S]
  [F.PreservesRightHomologyOf S] [G.PreservesRightHomologyOf S]

theorem homologyMap_mapNatTrans [S.HasHomology] (τ : F ⟶ G) :
    homologyMap (S.mapNatTrans τ) =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology ≫ (S.mapHomologyIso G).inv := (CategoryTheory.ShortComplex.LeftHomologyMapData.natTransApp S.homologyData.left τ).homologyMap_eq

