import Mathlib

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem smul_hom (x : CategoryTheory.Abelian.Ext X Y n) (r : R) [HasDerivedCategory C] :
    (r • x).hom = r • x.hom := by
  simp [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀]

