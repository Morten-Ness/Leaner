import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOneClass M] [MulOneClass N] [CommGroup G] [CommGroup H]

theorem comp_inv (φ : G →* H) (ψ : M →* G) : φ.comp ψ⁻¹ = (φ.comp ψ)⁻¹ := by
  ext
  simp

