import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem mk₀_hom [HasDerivedCategory.{w'} C] (f : X ⟶ Y) :
    (CategoryTheory.Abelian.Ext.mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map f) := by
  apply SmallShiftedHom.equiv_mk₀

