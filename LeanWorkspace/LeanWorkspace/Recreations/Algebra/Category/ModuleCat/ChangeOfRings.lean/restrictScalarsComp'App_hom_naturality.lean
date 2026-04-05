import Mathlib

variable {R₁ : Type u₁} {R₂ : Type u₂} {R₃ : Type u₃} [Ring R₁] [Ring R₂] [Ring R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃) (gf : R₁ →+* R₃)

variable (hgf : gf = g.comp f)

theorem restrictScalarsComp'App_hom_naturality {M N : ModuleCat R₃} (φ : M ⟶ N) :
    (ModuleCat.restrictScalars gf).map φ ≫ (ModuleCat.restrictScalarsComp'App f g gf hgf N).hom =
      (ModuleCat.restrictScalarsComp'App f g gf hgf M).hom ≫
        (ModuleCat.restrictScalars f).map ((ModuleCat.restrictScalars g).map φ) := (ModuleCat.restrictScalarsComp' f g gf hgf).hom.naturality φ

