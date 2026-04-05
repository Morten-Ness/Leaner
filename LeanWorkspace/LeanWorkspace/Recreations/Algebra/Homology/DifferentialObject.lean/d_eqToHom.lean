import Mathlib

variable {β : Type*} [AddCommGroup β] (b : β)

variable (V : Type*) [Category* V] [HasZeroMorphisms V]

theorem d_eqToHom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eqToHom (congr_arg X.X h) = X.d x z := by cases h; simp

