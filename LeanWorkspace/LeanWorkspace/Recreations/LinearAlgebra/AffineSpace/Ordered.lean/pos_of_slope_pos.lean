import Mathlib

variable {k E PE : Type*}

theorem pos_of_slope_pos {𝕜} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    {f : 𝕜 → 𝕜} {x₀ b : 𝕜}
    (hb : x₀ < b) (hbf : 0 < slope f x₀ b) (hf : f x₀ = 0) : 0 < f b := by
  simp_all [slope]

