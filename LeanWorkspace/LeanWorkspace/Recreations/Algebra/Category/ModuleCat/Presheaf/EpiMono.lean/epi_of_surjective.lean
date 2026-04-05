import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem epi_of_surjective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where
  left_cancellation g₁ g₂ hg := by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact congr_fun ((evaluation R X ⋙ forget _).congr_map hg) m₁

