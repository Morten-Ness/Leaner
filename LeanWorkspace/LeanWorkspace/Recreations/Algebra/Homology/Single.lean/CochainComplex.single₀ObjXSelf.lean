import Mathlib

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

theorem single₀ObjXSelf (X : V) :
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X = Iso.refl _ := rfl

