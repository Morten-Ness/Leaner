import Mathlib

variable {A : Type*}

variable {𝕜 : Type*} [Ring A] [PartialOrder A]

theorem _root_.isStrictlyPositive_algebraMap [ZeroLEOneClass A] [Semifield 𝕜] [PartialOrder 𝕜]
    [Algebra 𝕜 A] [PosSMulMono 𝕜 A] {c : 𝕜} (hc : 0 < c) :
    IsStrictlyPositive (algebraMap 𝕜 A c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact IsStrictlyPositive.smul hc isStrictlyPositive_one

