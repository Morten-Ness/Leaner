import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem g_apply_fromCoset (x : B) (y : X) :
    GrpCat.SurjectiveOfEpiAuxs.g x (fromCoset y) = fromCoset ⟨x • ↑y,
      by obtain ⟨z, hz⟩ := y.2; exact ⟨x * z, by simp [← hz, smul_smul]⟩⟩ := rfl

