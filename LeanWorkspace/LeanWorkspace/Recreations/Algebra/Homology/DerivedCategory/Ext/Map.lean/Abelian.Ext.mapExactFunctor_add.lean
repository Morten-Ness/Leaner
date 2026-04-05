import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

theorem Abelian.Ext.mapExactFunctor_add (f g : Ext.{w} X Y n) :
    (f + g).mapExactFunctor F = f.mapExactFunctor F + g.mapExactFunctor F := by
  aesop

