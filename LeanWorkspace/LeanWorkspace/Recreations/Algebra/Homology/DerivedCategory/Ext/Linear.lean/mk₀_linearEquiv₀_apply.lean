import Mathlib

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem mk₀_linearEquiv₀_apply (f : CategoryTheory.Abelian.Ext X Y 0) :
    mk₀ (CategoryTheory.Abelian.Ext.linearEquiv₀ (R := R) f) = f :=
  addEquiv₀.left_inv f

