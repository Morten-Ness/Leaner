import Mathlib

variable {J : Type v} [Category.{w} J]

variable (F : J ⥤ CommGrpCat.{u})

theorem hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget CommGrpCat).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

