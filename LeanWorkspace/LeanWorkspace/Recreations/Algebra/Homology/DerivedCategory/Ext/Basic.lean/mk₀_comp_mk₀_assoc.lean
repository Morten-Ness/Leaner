import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {n : ℕ} (α : CategoryTheory.Abelian.Ext Z T n) :
    (CategoryTheory.Abelian.Ext.mk₀ f).comp ((CategoryTheory.Abelian.Ext.mk₀ g).comp α (zero_add n)) (zero_add n) =
      (CategoryTheory.Abelian.Ext.mk₀ (f ≫ g)).comp α (zero_add n) := by
  rw [← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, CategoryTheory.Abelian.Ext.comp_assoc]
  lia

