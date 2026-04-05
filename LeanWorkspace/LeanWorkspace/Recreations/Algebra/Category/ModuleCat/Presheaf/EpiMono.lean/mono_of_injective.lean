import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem mono_of_injective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where
  right_cancellation {M} g₁ g₂ hg := by
    ext X m
    exact hf (congr_fun ((evaluation R X ⋙ forget _).congr_map hg) m)

