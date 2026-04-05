import Mathlib

variable {J : Type u} [Category.{v} J] {F : J ⥤ AddCommGrpCat.{w}} (c : Cocone F)

theorem hasColimit_iff_small_quot [DecidableEq J] : HasColimit F ↔ Small.{w} (Quot F) := ⟨fun _ ↦ Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((AddCommGrpCat.isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

