import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

theorem mk₀_homEquiv₀_apply (f : CategoryTheory.Abelian.Ext X Y 0) :
    CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.Abelian.Ext.homEquiv₀ f) = f := CategoryTheory.Abelian.Ext.homEquiv₀.left_inv f

