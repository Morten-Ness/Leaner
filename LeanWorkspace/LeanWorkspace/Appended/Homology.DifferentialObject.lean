import Mathlib

section

variable {β : Type*} [AddCommGroup β] {b : β}

variable {V : Type*} [Category* V] [HasZeroMorphisms V]

variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

theorem d_squared_apply {x : β} : X.d x ≫ X.d _ = 0 := congr_fun X.d_squared _

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.

end

section

variable {β : Type*} [AddCommGroup β] {b : β}

variable {V : Type*} [Category* V] [HasZeroMorphisms V]

variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

theorem objEqToHom_refl (i : β) : X.objEqToHom (refl i) = 𝟙 _ := rfl

-- Removing `@[simp]`, because it is in the opposite direction of `eqToHom_naturality`.
-- Having both causes an infinite loop in the simpNF linter.
set_option backward.isDefEq.respectTransparency false in -- Needed in dgoToHomologicalComplex

end
