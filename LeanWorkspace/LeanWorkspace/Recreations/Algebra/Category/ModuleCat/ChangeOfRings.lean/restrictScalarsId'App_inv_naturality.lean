import Mathlib

variable {R : Type u₁} [Ring R] (f : R →+* R)

variable (hf : f = RingHom.id R)

theorem restrictScalarsId'App_inv_naturality {M N : ModuleCat R} (φ : M ⟶ N) :
    φ ≫ (ModuleCat.restrictScalarsId'App f hf N).inv =
      (ModuleCat.restrictScalarsId'App f hf M).inv ≫ (ModuleCat.restrictScalars f).map φ := (ModuleCat.restrictScalarsId' f hf).inv.naturality φ

