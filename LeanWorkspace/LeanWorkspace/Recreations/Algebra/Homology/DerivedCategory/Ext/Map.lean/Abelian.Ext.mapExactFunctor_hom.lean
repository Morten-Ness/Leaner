import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

set_option backward.isDefEq.respectTransparency false in
theorem Abelian.Ext.mapExactFunctor_hom
    [HasDerivedCategory.{t} C] [HasDerivedCategory.{t'} D]
    [HasExt.{w} C] [HasExt.{w'} D] {X Y : C} {n : ℕ} (e : Ext X Y n) :
    (e.mapExactFunctor F).hom =
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ e.hom.map F.mapDerivedCategory ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' := by
  have : (e.mapExactFunctor F).hom = _ :=
    ((F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (.up ℤ)).equiv_smallShiftedHomMap DerivedCategory.Q DerivedCategory.Q
        ((F.mapCochainComplexSingleFunctor 0).app X) ((F.mapCochainComplexSingleFunctor 0).app Y)
          F.mapDerivedCategory F.mapDerivedCategoryFactors.symm e)
  rw [this, ← ShiftedHom.comp_mk₀ _ 0 rfl, ← ShiftedHom.mk₀_comp 0 rfl]
  congr 2
  · dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp only [Category.comp_id, Category.id_comp, Category.assoc]
    congr 1
    change _ = _ ≫ F.mapDerivedCategory.map (𝟙 _)
    simp
  · congr 1
    dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp only [map_id, Category.id_comp, NatIso.cancel_natIso_hom_left, comp_obj]
    exact (Category.comp_id _).symm

