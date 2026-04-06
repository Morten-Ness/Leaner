import Mathlib

variable {A : Type*}

variable {𝕜 : Type*} [Ring A] [PartialOrder A]

theorem spectrum_pos [CommSemiring 𝕜] [PartialOrder 𝕜] [Algebra 𝕜 A]
    [NonnegSpectrumClass 𝕜 A] {a : A} (ha : IsStrictlyPositive a) {x : 𝕜}
    (hx : x ∈ spectrum 𝕜 a) : 0 < x := by
  exact ha.spectrum_pos hx
