import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable (M : ModuleCat.{v} R)

theorem map'_comp {M₁ M₂ M₃ : ModuleCat.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
    ModuleCat.ExtendScalars.map' f (l₁₂ ≫ l₂₃) = ModuleCat.ExtendScalars.map' f l₁₂ ≫ ModuleCat.ExtendScalars.map' f l₂₃ := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul => rfl
  | add _ _ ihx ihy => grind

