import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

variable [HasExt.{w} C]

variable {X Y Z T : C}

variable [HasDerivedCategory.{w'} C]

theorem comp_hom {a b : ℕ} (α : CategoryTheory.Abelian.Ext X Y a) (β : CategoryTheory.Abelian.Ext Y Z b) {c : ℕ} (h : a + b = c) :
    (α.comp β h).hom = α.hom.comp β.hom (by lia) := by
  apply SmallShiftedHom.equiv_comp

