import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

variable {S : ShortComplex C} (hS : S.ShortExact) (Y : C)

theorem singleFunctor_map_comp_hom [HasDerivedCategory.{w'} C]
    {X Y Z : C} (f : X ⟶ Y) {n : ℕ} (x : CategoryTheory.Abelian.Ext Y Z n) :
    (DerivedCategory.singleFunctor C 0).map f ≫ x.hom =
      ((mk₀ f).comp x (zero_add n)).hom := by
  simp only [comp_hom, mk₀_hom, ShiftedHom.mk₀_comp]

