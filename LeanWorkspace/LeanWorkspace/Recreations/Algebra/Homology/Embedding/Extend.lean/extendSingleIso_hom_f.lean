import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

variable [DecidableEq ι'] (i : ι) (i' : ι')

theorem extendSingleIso_hom_f (h : e.f i = i') :
    (HomologicalComplex.extendSingleIso e HomologicalComplex.extend.X i i' h).hom.f i' =
      (((single C c i).obj HomologicalComplex.extend.X).extendXIso e h).hom ≫ (singleObjXSelf c i HomologicalComplex.extend.X).hom ≫
        (singleObjXSelf c' i' HomologicalComplex.extend.X).inv := by
  simp [HomologicalComplex.extendSingleIso]

