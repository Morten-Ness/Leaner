import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) (n : ℕ)

theorem Functor.mapExtAddHom_coe : ⇑(F.mapExtAddHom X Y n) = Ext.mapExactFunctor F := rfl

