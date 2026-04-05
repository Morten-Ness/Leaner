import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

theorem NatTrans.mapHomologicalComplex_id
    (c : ComplexShape ι) (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] :
    CategoryTheory.NatTrans.mapHomologicalComplex (𝟙 F) c = 𝟙 (F.mapHomologicalComplex c) := by cat_disch

