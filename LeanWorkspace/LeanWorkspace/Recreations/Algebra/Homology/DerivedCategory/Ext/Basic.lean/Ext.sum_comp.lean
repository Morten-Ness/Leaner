import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

private theorem add_hom' (α β : CategoryTheory.Abelian.Ext X Y n) : (α + β).hom' = α.hom' + β.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem neg_hom' (α : CategoryTheory.Abelian.Ext X Y n) : (-α).hom' = -α.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem zero_hom' : (0 : CategoryTheory.Abelian.Ext X Y n).hom' = 0 := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


theorem Ext.sum_comp {X Y Z : C} {p : ℕ} {ι : Type*} [Fintype ι] (α : ι → CategoryTheory.Abelian.Ext X Y p) {q : ℕ}
    (β : CategoryTheory.Abelian.Ext Y Z q) {n : ℕ} (h : p + q = n) :
    (∑ i, α i).comp β h = ∑ i, (α i).comp β h := map_sum (β.postcomp X h) _ _

