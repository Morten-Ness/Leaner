import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

variable {n : ℕ}

private theorem add_hom' (α β : CategoryTheory.Abelian.Ext X Y n) : (α + β).hom' = α.hom' + β.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem neg_hom' (α : CategoryTheory.Abelian.Ext X Y n) : (-α).hom' = -α.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem zero_hom' : (0 : CategoryTheory.Abelian.Ext X Y n).hom' = 0 := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


theorem mk₀_neg (f : X ⟶ Y) :
    CategoryTheory.Abelian.Ext.mk₀ (-f) = -CategoryTheory.Abelian.Ext.mk₀ f := by
  letI := HasDerivedCategory.standard C; CategoryTheory.Abelian.Ext.ext; simp [neg_hom']

