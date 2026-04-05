import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem epi_iff_surjective :
    Epi f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X) := ⟨fun _ ↦ PresheafOfModules.surjective_of_epi f, PresheafOfModules.epi_of_surjective⟩

