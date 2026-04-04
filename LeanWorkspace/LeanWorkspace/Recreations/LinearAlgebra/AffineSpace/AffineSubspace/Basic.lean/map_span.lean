import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem map_span (s : Set P₁) : (affineSpan k s).map f = affineSpan k (f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
  apply ext_of_direction_eq
  · simp [direction_affineSpan]
  · exact ⟨f p, mem_image_of_mem f (subset_affineSpan k _ hp),
          subset_affineSpan k _ (mem_image_of_mem f hp)⟩

