import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

theorem NatTrans.app_homology {F G : C ⥤ D} (τ : F ⟶ G)
    (S : ShortComplex C) [S.HasHomology] [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [G.PreservesRightHomologyOf S] :
    τ.app S.homology = (S.mapHomologyIso F).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom := by
  rw [ShortComplex.homologyMap_mapNatTrans, assoc, assoc, Iso.inv_hom_id,
    comp_id, Iso.inv_hom_id_assoc]

