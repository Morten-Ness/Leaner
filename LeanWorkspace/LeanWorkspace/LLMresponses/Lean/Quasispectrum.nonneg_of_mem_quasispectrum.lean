import Mathlib

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

theorem nonneg_of_mem_quasispectrum {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PartialOrder A]
    [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : 0 ≤ a) {x : 𝕜}
    (hx : x ∈ quasispectrum 𝕜 a) : 0 ≤ x := by
  simpa using NonnegSpectrumClass.nonneg_of_mem_quasispectrum (𝕜 := 𝕜) ha hx
