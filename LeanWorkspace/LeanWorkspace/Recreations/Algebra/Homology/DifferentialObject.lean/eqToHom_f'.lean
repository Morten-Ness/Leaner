import Mathlib

variable {β : Type*} [AddCommGroup β] {b : β}

variable {V : Type*} [Category* V] [HasZeroMorphisms V]

variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

theorem eqToHom_f' {X Y : CategoryTheory.DifferentialObject ℤ (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β}
    (h : x = y) : X.objEqToHom h ≫ f.f y = f.f x ≫ Y.objEqToHom h := by cases h; simp

