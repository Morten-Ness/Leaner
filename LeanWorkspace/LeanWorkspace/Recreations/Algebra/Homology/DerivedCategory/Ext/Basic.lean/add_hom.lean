import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

variable {n : ℕ}

variable [HasDerivedCategory.{w'} C]

private theorem add_hom' (α β : CategoryTheory.Abelian.Ext X Y n) : (α + β).hom' = α.hom' + β.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem neg_hom' (α : CategoryTheory.Abelian.Ext X Y n) : (-α).hom' = -α.hom' := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


private theorem zero_hom' : (0 : CategoryTheory.Abelian.Ext X Y n).hom' = 0 := letI := HasDerivedCategory.standard C
  CategoryTheory.Abelian.Ext.homEquiv.symm.injective (Equiv.symm_apply_apply _ _)


theorem add_hom (α β : CategoryTheory.Abelian.Ext X Y n) : (α + β).hom = α.hom + β.hom := by
  let α' : CategoryTheory.Abelian.Ext (X ⊞ X) Y n := (CategoryTheory.Abelian.Ext.mk₀ biprod.fst).comp α (zero_add n)
  let β' : CategoryTheory.Abelian.Ext (X ⊞ X) Y n := (CategoryTheory.Abelian.Ext.mk₀ biprod.snd).comp β (zero_add n)
  have eq₁ : α + β = (CategoryTheory.Abelian.Ext.mk₀ (biprod.lift (𝟙 X) (𝟙 X))).comp (α' + β') (zero_add n) := by
    simp [α', β']
  have eq₂ : α' + β' = CategoryTheory.Abelian.Ext.homEquiv.symm (α'.hom + β'.hom) := by
    apply CategoryTheory.Abelian.Ext.biprod_ext
    all_goals CategoryTheory.Abelian.Ext.ext; simp [α', β', ← Functor.map_comp]
  simp only [eq₁, eq₂, CategoryTheory.Abelian.Ext.comp_hom, Equiv.apply_symm_apply, ShiftedHom.comp_add]
  congr
  · dsimp [α']
    rw [CategoryTheory.Abelian.Ext.comp_hom, CategoryTheory.Abelian.Ext.mk₀_hom, CategoryTheory.Abelian.Ext.mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      biprod.lift_fst, Functor.map_id, ShiftedHom.mk₀_id_comp]
  · dsimp [β']
    rw [CategoryTheory.Abelian.Ext.comp_hom, CategoryTheory.Abelian.Ext.mk₀_hom, CategoryTheory.Abelian.Ext.mk₀_hom]
    dsimp
    rw [ShiftedHom.mk₀_comp_mk₀_assoc, ← Functor.map_comp,
      biprod.lift_snd, Functor.map_id, ShiftedHom.mk₀_id_comp]

