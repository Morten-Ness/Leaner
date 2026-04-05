import Mathlib

variable {A : Type*}

variable {𝕜 : Type*} [Ring A] [PartialOrder A]

theorem spectrum_pos [CommSemiring 𝕜] [PartialOrder 𝕜] [Algebra 𝕜 A]
    [NonnegSpectrumClass 𝕜 A] {a : A} (ha : IsStrictlyPositive a) {x : 𝕜}
    (hx : x ∈ spectrum 𝕜 a) : 0 < x := by
  have h₁ : 0 ≤ x := by grind
  have h₂ : x ≠ 0 := by grind [= spectrum.zero_notMem_iff]
  exact lt_of_le_of_ne h₁ h₂.symm

grind_pattern IsStrictlyPositive.spectrum_pos => x ∈ spectrum 𝕜 a, IsStrictlyPositive a

