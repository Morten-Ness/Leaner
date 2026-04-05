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

theorem singleMapHomologicalComplex_inv_app_ne {i j : ι} (h : i ≠ j) (X : W₁) :
    ((HomologicalComplex.singleMapHomologicalComplex F c j).inv.app X).f i = 0 := by
  simp [HomologicalComplex.singleMapHomologicalComplex, h]

