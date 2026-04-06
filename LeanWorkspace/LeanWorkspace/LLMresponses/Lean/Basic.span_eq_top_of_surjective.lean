FAIL
import Mathlib

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f)
    (h : affineSpan k s = ⊤) : affineSpan k (f '' s) = ⊤ := by
  rw [eq_top_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  rw [← h] at hy
  exact affineSpan_mono (show s ⊆ f '' s from fun z hz => ⟨z, hz, rfl⟩) hy
