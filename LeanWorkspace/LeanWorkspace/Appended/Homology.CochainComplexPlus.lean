import Mathlib

section

variable (C : Type*) [Category* C]

variable [HasZeroMorphisms C]

theorem mono_iff [HasLimitsOfShape WalkingCospan C] {X Y : CochainComplex.Plus C} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom := ⟨fun _ ↦ inferInstanceAs (Mono ((ι C).map f)),
    fun _ ↦ Functor.mono_of_mono_map (ι C) (by assumption)⟩

end
