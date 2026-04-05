import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

private theorem add_hom' (α β : CategoryTheory.Abelian.Ext X Y n) : (α + β).hom' = α.hom' + β.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem neg_hom' (α : CategoryTheory.Abelian.Ext X Y n) : (-α).hom' = -α.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem zero_hom' : (0 : CategoryTheory.Abelian.Ext X Y n).hom' = 0 := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


theorem hasExt_iff_small_ext :
    HasExt.{w'} C ↔ ∀ (X Y : C) (n : ℕ), Small.{w'} (CategoryTheory.Abelian.Ext.{w} X Y n) := by
  letI := HasDerivedCategory.standard C
  simp only [CategoryTheory.hasExt_iff, small_congr CategoryTheory.Abelian.Ext.homEquiv]
  constructor
  · intro h X Y n
    exact h X Y n (by simp)
  · intro h X Y n hn
    lift n to ℕ using hn
    exact h X Y n

