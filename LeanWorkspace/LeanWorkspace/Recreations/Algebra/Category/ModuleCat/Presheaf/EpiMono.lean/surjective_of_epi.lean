import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem surjective_of_epi [Epi f] (X : Cᵒᵖ) :
    Function.Surjective (f.app X) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

