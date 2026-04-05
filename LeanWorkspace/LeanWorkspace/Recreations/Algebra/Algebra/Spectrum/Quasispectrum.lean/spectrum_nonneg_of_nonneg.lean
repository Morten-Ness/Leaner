import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem spectrum_nonneg_of_nonneg {𝕜 A : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
    [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] ⦃a : A⦄ (ha : 0 ≤ a) ⦃x : 𝕜⦄ (hx : x ∈ spectrum 𝕜 a) :
    0 ≤ x := NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg a ha x (spectrum_subset_quasispectrum 𝕜 a hx)

grind_pattern spectrum_nonneg_of_nonneg => x ∈ spectrum 𝕜 a

