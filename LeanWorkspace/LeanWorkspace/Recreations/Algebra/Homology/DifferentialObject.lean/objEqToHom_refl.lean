import Mathlib

variable {β : Type*} [AddCommGroup β] {b : β}

variable {V : Type*} [Category* V] [HasZeroMorphisms V]

variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

theorem objEqToHom_refl (i : β) : X.objEqToHom (refl i) = 𝟙 _ := rfl

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.
set_option backward.isDefEq.respectTransparency false in -- Needed in dgoToHomologicalComplex

