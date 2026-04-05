FAIL
import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) :
    (affineSpan k s).comap (f : P₁ →ᵃ[k] P₂) = affineSpan k (f ⁻¹' s) := by
  ext p
  change f p ∈ affineSpan k s ↔ p ∈ affineSpan k (f ⁻¹' s)
  constructor
  · intro hp
    refine affineSpan_le ?_ hp
    intro q hq
    change f q ∈ affineSpan k s
    exact AffineSubspace.subset_span hq
  · intro hp
    have hmap : (affineSpan k (f ⁻¹' s)).map (f : P₁ →ᵃ[k] P₂) = affineSpan k s := by
      rw [AffineEquiv.image_affineSpan]
      simpa [Set.image_preimage_eq_iff, f.surjective.subset_range]
    have hfp : f p ∈ (affineSpan k (f ⁻¹' s)).map (f : P₁ →ᵃ[k] P₂) := by
      rw [← hmap]
      exact ⟨p, hp, rfl⟩
    simpa using hfp
