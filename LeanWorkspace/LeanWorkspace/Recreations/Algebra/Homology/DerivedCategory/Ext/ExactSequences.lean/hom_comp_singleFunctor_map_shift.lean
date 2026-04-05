import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem hom_comp_singleFunctor_map_shift [HasDerivedCategory.{w'} C]
    {X Y Z : C} {n : ℕ} (x : CategoryTheory.Abelian.Ext X Y n) (f : Y ⟶ Z) :
    x.hom ≫ ((DerivedCategory.singleFunctor C 0).map f)⟦(n : ℤ)⟧' =
      (x.comp (mk₀ f) (add_zero n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.comp_mk₀]

