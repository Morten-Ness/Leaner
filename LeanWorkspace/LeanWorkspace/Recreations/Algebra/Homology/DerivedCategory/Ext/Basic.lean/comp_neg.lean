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


theorem comp_neg (α : CategoryTheory.Abelian.Ext X Y n) {m : ℕ} (β : CategoryTheory.Abelian.Ext Y Z m) {p : ℕ} (h : n + m = p) :
    α.comp (-β) h = -α.comp β h := by
  letI := HasDerivedCategory.standard C; CategoryTheory.Abelian.Ext.ext; simp [this, neg_hom']

