import Mathlib

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem epi_iff_surjective :
    Epi f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X) := ⟨fun _ ↦ PresheafOfModules.surjective_of_epi f, PresheafOfModules.epi_of_surjective⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem epi_of_surjective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where
  left_cancellation g₁ g₂ hg := by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact congr_fun ((evaluation R X ⋙ forget _).congr_map hg) m₁

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem injective_of_mono [Mono f] (X : Cᵒᵖ) :
    Function.Injective (f.app X) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem mono_iff_surjective :
    Mono f ↔ ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X) := ⟨fun _ ↦ PresheafOfModules.injective_of_mono f, PresheafOfModules.mono_of_injective⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem mono_of_injective (hf : ∀ ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where
  right_cancellation {M} g₁ g₂ hg := by
    ext X m
    exact hf (congr_fun ((evaluation R X ⋙ forget _).congr_map hg) m)

end

section

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

theorem surjective_of_epi [Epi f] (X : Cᵒᵖ) :
    Function.Surjective (f.app X) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

end
