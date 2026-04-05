import Mathlib

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

theorem ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars.{_, _, u} f) := by
  have : PreservesFiniteLimits (extendScalars.{_, _, u} f ⋙ restrictScalars.{_, _, u} f) :=
    ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat hf
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars f) (restrictScalars f)

