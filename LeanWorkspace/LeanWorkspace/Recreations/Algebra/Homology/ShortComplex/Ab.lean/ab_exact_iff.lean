import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ab_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [CategoryTheory.ShortComplex.exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩

