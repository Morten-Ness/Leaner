import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

variable [DecidableEq ι'] (i : ι) (i' : ι')

theorem extendSingleIso_inv_f (h : e.f i = i') :
    (HomologicalComplex.extendSingleIso e HomologicalComplex.extend.X i i' h).inv.f i' =
      (singleObjXSelf c' i' HomologicalComplex.extend.X).hom ≫ (singleObjXSelf c i HomologicalComplex.extend.X).inv ≫
        (((single C c i).obj HomologicalComplex.extend.X).extendXIso e h).inv := by
  simp [HomologicalComplex.extendSingleIso]

