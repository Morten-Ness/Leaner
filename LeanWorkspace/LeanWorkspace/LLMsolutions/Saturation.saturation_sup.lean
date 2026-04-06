FAIL
import Mathlib

variable {M : Type*} [MulOneClass M]

theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := by
  apply le_antisymm
  · exact sup_le (Submonoid.saturation_mono le_sup_left) (Submonoid.saturation_mono le_sup_right)
  · exact Submonoid.saturation_le.2 (sup_le (Submonoid.subset_saturation _) (Submonoid.subset_saturation _))
