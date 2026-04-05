import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem mono_iff_surjective :
    Mono f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X) := ⟨fun _ ↦ PresheafOfModules.injective_of_mono f, PresheafOfModules.mono_of_injective⟩

