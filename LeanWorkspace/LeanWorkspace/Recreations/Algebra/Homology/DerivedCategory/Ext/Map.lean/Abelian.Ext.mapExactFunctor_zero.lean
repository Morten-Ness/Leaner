import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

theorem Abelian.Ext.mapExactFunctor_zero : (0 : Ext X Y n).mapExactFunctor F = 0 := by
  aesop

