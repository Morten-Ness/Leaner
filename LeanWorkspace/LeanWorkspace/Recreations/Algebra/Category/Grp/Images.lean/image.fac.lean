import Mathlib

variable {G H : AddCommGrpCat.{0}} (f : G ⟶ H)

theorem image.fac : AddCommGrpCat.factorThruImage f ≫ AddCommGrpCat.image.ι f = f := by
  ext
  rfl

attribute [local simp] AddCommGrpCat.image.fac

