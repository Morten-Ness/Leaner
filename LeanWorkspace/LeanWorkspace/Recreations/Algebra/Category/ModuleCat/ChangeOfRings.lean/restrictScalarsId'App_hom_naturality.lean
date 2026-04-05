import Mathlib

variable {R : Type u₁} [Ring R] (f : R →+* R)

variable (hf : f = RingHom.id R)

theorem restrictScalarsId'App_hom_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    (ModuleCat.restrictScalars f).map φ ≫ (ModuleCat.restrictScalarsId'App f hf N).hom =
      (ModuleCat.restrictScalarsId'App f hf M).hom ≫ φ := (ModuleCat.restrictScalarsId' f hf).hom.naturality φ

