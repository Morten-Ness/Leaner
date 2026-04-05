import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) :
    (CategoryTheory.Abelian.Ext.mk₀ f).comp (CategoryTheory.Abelian.Ext.mk₀ g) (zero_add 0) = CategoryTheory.Abelian.Ext.mk₀ (f ≫ g) := by
  letI := HasDerivedCategory.standard C; CategoryTheory.Abelian.Ext.ext; simp

