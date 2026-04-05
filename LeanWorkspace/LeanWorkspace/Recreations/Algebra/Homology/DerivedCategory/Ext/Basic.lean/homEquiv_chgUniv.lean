import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable [HasExt.{w'} C] {X Y : C} {n : ℕ}

private theorem add_hom' (α β : CategoryTheory.Abelian.Ext X Y n) : (α + β).hom' = α.hom' + β.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem neg_hom' (α : CategoryTheory.Abelian.Ext X Y n) : (-α).hom' = -α.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem zero_hom' : (0 : CategoryTheory.Abelian.Ext X Y n).hom' = 0 := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


theorem homEquiv_chgUniv [HasDerivedCategory.{w''} C] (e : CategoryTheory.Abelian.Ext.{w} X Y n) :
    CategoryTheory.Abelian.Ext.homEquiv.{w'', w'} (CategoryTheory.Abelian.Ext.chgUniv.{w'} e) = CategoryTheory.Abelian.Ext.homEquiv.{w'', w} e := by
  apply SmallShiftedHom.equiv_chgUniv

