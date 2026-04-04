import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem AffineMap.map_vectorSpan {s : Set P₁} :
    Submodule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s) := by
  simp [vectorSpan_def, f.image_vsub_image]

-- this name was backwards

