import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem hasExt_of_hasDerivedCategory [HasDerivedCategory.{w} C] : HasExt.{w} C := by
  rw [CategoryTheory.hasExt_iff.{w}]
  infer_instance

