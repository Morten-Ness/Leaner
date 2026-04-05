import Mathlib

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{v}}

theorem isSeparating : ObjectProperty.IsSeparating (PresheafOfModules.freeYoneda R) := by
  intro M N f₁ f₂ h
  ext ⟨X⟩ m
  obtain ⟨g, rfl⟩ := PresheafOfModules.freeYonedaEquiv.surjective m
  exact congr_arg PresheafOfModules.freeYonedaEquiv (h _ ⟨X⟩ g)

