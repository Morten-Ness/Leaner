import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ ∀ a : A, 0 ≤ a → ∀ x ∈ spectrum 𝕜 a, 0 ≤ x := by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ ↦ h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg

