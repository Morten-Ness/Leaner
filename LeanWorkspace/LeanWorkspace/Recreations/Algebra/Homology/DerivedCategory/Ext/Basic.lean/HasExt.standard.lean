import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

theorem HasExt.standard : HasExt.{max u v} C := by
  letI := HasDerivedCategory.standard
  exact CategoryTheory.hasExt_of_hasDerivedCategory _

