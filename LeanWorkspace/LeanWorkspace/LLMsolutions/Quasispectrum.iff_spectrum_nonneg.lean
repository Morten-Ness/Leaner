FAIL
import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ ∀ a : A, 0 ≤ a → ∀ x ∈ spectrum 𝕜 a, 0 ≤ x := by
  constructor
  · intro h a ha x hx
    exact h.quasispectrum_nonneg_of_nonneg a ha x (by
      rwa [quasispectrum_eq_spectrum] )
  · intro h
    exact
      { quasispectrum_nonneg_of_nonneg := by
          intro a ha x hx
          exact h a ha x (by rwa [quasispectrum_eq_spectrum] at hx) }
