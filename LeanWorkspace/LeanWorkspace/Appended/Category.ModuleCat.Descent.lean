import Mathlib

section

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

theorem ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars.{_, _, u} f) := by
  have : PreservesFiniteLimits (extendScalars.{_, _, u} f ⋙ restrictScalars.{_, _, u} f) :=
    ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat hf
  exact preservesFiniteLimits_of_reflects_of_preserves (extendScalars f) (restrictScalars f)

end

section

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

theorem ModuleCat.preservesFiniteLimits_tensorLeft_of_ringHomFlat (hf : f.Flat) :
    PreservesFiniteLimits <| tensorLeft ((restrictScalars f).obj (ModuleCat.of B B)) := by
  algebraize [f]
  change PreservesFiniteLimits <| tensorLeft (ModuleCat.of A B)
  infer_instance

end

section

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}

theorem ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat
    (hf : f.FaithfullyFlat) : (extendScalars.{_, _, u} f).ReflectsIsomorphisms := by
  refine ⟨fun {M N} g h ↦ ?_⟩
  algebraize [f]
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  replace h : Function.Bijective (LinearMap.lTensor B g.hom) := h
  rwa [Module.FaithfullyFlat.lTensor_bijective_iff_bijective] at h

end
