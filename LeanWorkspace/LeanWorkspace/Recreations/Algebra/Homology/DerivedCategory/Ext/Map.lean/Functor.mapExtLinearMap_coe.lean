import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

variable (R : Type*) [Ring R] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [F.Linear R]

theorem Functor.mapExtLinearMap_coe : ⇑(F.mapExtLinearMap R X Y n) = Ext.mapExactFunctor F := rfl

