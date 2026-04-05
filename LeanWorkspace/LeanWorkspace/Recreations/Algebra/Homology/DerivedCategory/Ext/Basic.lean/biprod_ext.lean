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


theorem biprod_ext {X₁ X₂ : C} {α β : CategoryTheory.Abelian.Ext (X₁ ⊞ X₂) Y n}
    (h₁ : (CategoryTheory.Abelian.Ext.mk₀ biprod.inl).comp α (zero_add n) = (CategoryTheory.Abelian.Ext.mk₀ biprod.inl).comp β (zero_add n))
    (h₂ : (CategoryTheory.Abelian.Ext.mk₀ biprod.inr).comp α (zero_add n) = (CategoryTheory.Abelian.Ext.mk₀ biprod.inr).comp β (zero_add n)) :
    α = β := by
  letI := HasDerivedCategory.standard C
  rw [CategoryTheory.Abelian.Ext.ext_iff] at h₁ h₂ ⊢
  simp only [CategoryTheory.Abelian.Ext.comp_hom, CategoryTheory.Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp] at h₁ h₂
  apply BinaryCofan.IsColimit.hom_ext
    (isBinaryBilimitOfPreserves (singleFunctor C 0)
      (BinaryBiproduct.isBilimit X₁ X₂)).isColimit
  all_goals assumption

