import Mathlib

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C]

variable {X Y : C} {n : ℕ}

theorem smul_comp {X Y Z : C} {a b : ℕ} (α : CategoryTheory.Abelian.Ext X Y a) (β : CategoryTheory.Abelian.Ext Y Z b)
    {c : ℕ} (h : a + b = c) (r : R) :
    (r • α).comp β h = r • α.comp β h := by
  let := HasDerivedCategory.standard C
  aesop

