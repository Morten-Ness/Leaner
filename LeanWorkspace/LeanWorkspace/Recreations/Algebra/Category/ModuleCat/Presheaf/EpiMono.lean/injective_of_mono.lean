import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem injective_of_mono [Mono f] (X : Cᵒᵖ) :
    Function.Injective (f.app X) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

