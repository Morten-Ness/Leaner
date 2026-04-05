import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ : Type*} [Category* W₁] [Category* W₂] [HasZeroMorphisms W₁] [HasZeroMorphisms W₂]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

variable [HasZeroObject W₁] [HasZeroObject W₂]

variable (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms]
    (c : ComplexShape ι) [DecidableEq ι]

theorem singleMapHomologicalComplex_hom_app_self (j : ι) (X : W₁) :
    ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app X).f j =
      F.map (singleObjXSelf c j X).hom ≫ (singleObjXSelf c j (F.obj X)).inv := by
  simp [HomologicalComplex.singleMapHomologicalComplex, singleObjXSelf, singleObjXIsoOfEq, eqToHom_map]

