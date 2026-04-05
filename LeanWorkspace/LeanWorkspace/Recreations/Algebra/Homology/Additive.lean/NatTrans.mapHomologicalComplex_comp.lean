import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

theorem NatTrans.mapHomologicalComplex_comp (c : ComplexShape ι) {F G H : W₁ ⥤ W₂}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (α : F ⟶ G) (β : G ⟶ H) :
    CategoryTheory.NatTrans.mapHomologicalComplex (α ≫ β) c =
      CategoryTheory.NatTrans.mapHomologicalComplex α c ≫ CategoryTheory.NatTrans.mapHomologicalComplex β c := by
  cat_disch

