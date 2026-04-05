import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Preadditive C₁] [Preadditive C₂]
  {K L : HomologicalComplex C₁ c} (φ : K ⟶ L) (F : C₁ ⥤ C₂) [F.Additive]
  [F.PreservesHomology]

variable (i : ι) [K.HasHomology i] [L.HasHomology i]
  [((F.mapHomologicalComplex c).obj K).HasHomology i]
  [((F.mapHomologicalComplex c).obj L).HasHomology i]

theorem quasiIsoAt_map_iff_of_preservesHomology [F.ReflectsIsomorphisms] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map φ) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_iff_of_preservesLeftHomology F
    ((shortComplexFunctor C₁ c i).map φ)

