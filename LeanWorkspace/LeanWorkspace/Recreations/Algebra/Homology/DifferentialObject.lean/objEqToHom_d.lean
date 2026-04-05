import Mathlib

variable {β : Type*} [AddCommGroup β] {b : β}

variable {V : Type*} [Category* V] [HasZeroMorphisms V]

variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

theorem objEqToHom_d {x y : β} (h : x = y) :
    X.objEqToHom h ≫ X.d y = X.d x ≫ X.objEqToHom (by cases h; rfl) := by cases h; simp

