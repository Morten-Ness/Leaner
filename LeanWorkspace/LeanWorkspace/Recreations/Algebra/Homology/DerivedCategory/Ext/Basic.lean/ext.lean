import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

variable [HasDerivedCategory.{w'} C]

theorem ext {n : ℕ} {α β : CategoryTheory.Abelian.Ext X Y n} (h : α.hom = β.hom) : α = β := CategoryTheory.Abelian.Ext.homEquiv.injective h

