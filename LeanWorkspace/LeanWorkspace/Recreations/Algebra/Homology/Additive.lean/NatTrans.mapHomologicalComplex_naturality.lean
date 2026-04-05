import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

theorem NatTrans.mapHomologicalComplex_naturality {c : ComplexShape ι} {F G : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (α : F ⟶ G) {C D : HomologicalComplex W₁ c} (f : C ⟶ D) :
    (F.mapHomologicalComplex c).map f ≫ (CategoryTheory.NatTrans.mapHomologicalComplex α c).app D =
      (CategoryTheory.NatTrans.mapHomologicalComplex α c).app C ≫ (G.mapHomologicalComplex c).map f := by
  simp

